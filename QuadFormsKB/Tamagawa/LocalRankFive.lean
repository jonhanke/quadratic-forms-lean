/-
# Forms of rank 5 over a non-archimedean completion are isotropic

For a number field $F$ and a finite place $v$ (a nonzero prime $\mathfrak p$ of $\mathcal O_F$), every nondegenerate quadratic
form of rank $5$ over the completion $F_v$ is isotropic (`localRankFiveIsotropic`). This discharges the input
`Quat.LocalRankFiveIsotropic F`, so the surjectivity of the reduced norm at every finite place and **Eichler's norm theorem**
become unconditional (`Quat.exists_nrd_eq_finite'`, `Quat.eichler_norm_theorem'`).

*Proof* (Serre 1973, Ch. IV, §2.2, Thm. 6, adapted to $F_v$; only three local facts are used, all proved in this repository
for every finite place, dyadic included):
* the Hilbert symbol $(\cdot,\cdot)_v$ is multiplicative (`HN.hilbertSymbol_mul_left_finite_nf`);
* it is nondegenerate: a non-square $c$ has $(x,c)_v = -1$ for some $x$ (`SqDual.hilbCl_nondeg_fin`);
* $[F_v^\times : F_v^{\times2}] = 4\,N\mathfrak p^{\operatorname{ord}_v 2} \ge 4$ (`HN.index_sq_completion`).

1. *Binary forms.* For $a, b, t \in F_v^\times$, $\langle a,b\rangle$ represents $t$ iff $(t, -ab)_v = (a,b)_v$
   (`represents_two_iff`).
2. *Quaternary forms with non-square determinant are isotropic* (`isotropic_four_of_not_isSquare`). If $-b_0b_1$ or
   $-b_2b_3$ is a square, a binary half is isotropic. Otherwise the characters $(\cdot,-b_0b_1)$, $(\cdot,-b_2b_3)$ are
   distinct and nontrivial (their product $(\cdot, b_0b_1b_2b_3)$ is nontrivial), so jointly surjective onto $\{\pm1\}^2$; pick
   $t$ represented by $\langle b_0,b_1\rangle$ with $-t$ represented by $\langle b_2,b_3\rangle$.
3. *Rank 5* (`isotropic_diag_five`). For $\langle a_0,\dots,a_4\rangle$, the values $t$ of $\langle a_0,a_1\rangle$ fill a
   coset of the index-$2$ kernel of $(\cdot,-a_0a_1)_v$ in $F_v^\times/F_v^{\times2}$, which has at least $2$ elements since
   the group has at least $4$; so some value $t$ has $t\,a_2a_3a_4$ a non-square, and $\langle t,a_2,a_3,a_4\rangle$ is isotropic
   by step 2.
4. Diagonalize (`FieldGen.exists_isometric_diag`).

Indices are 0-based. Over $\mathbb Q_p$ the same theorem is `RankFive.isotropic_padic_diag_odd` /
`RankFive.isotropic_two_adic_diag` (rational diagonal forms).
-/
import QuadFormsKB.Tamagawa.EichlerNorm
import QuadFormsKB.Tamagawa.SquareClassDuality
import QuadFormsKB.Literature.LocalGlobal.FieldGeneral

open NumberField IsDedekindDomain Quaternion

noncomputable section

namespace QuadFormsKB.LocalRankFive

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Kv" => v.adicCompletion F

local notation "hs" => hilbertSymbol (v.adicCompletion F)

/-! ### Hilbert-symbol arithmetic at a finite place -/

theorem hs_pm (a b : Kv) : hs a b = 1 ∨ hs a b = -1 := HN.hilbertSymbol_eq_one_or _ a b

theorem hs_mul_left {a a' b : Kv} (ha : a ≠ 0) (ha' : a' ≠ 0) (hb : b ≠ 0) :
    hs (a * a') b = hs a b * hs a' b :=
  HN.hilbertSymbol_mul_left_finite_nf v a a' b ha ha' hb

theorem hs_mul_right {a b b' : Kv} (ha : a ≠ 0) (hb : b ≠ 0) (hb' : b' ≠ 0) :
    hs a (b * b') = hs a b * hs a b' := by
  rw [hilbertSymbol_comm, hs_mul_left v hb hb' ha, hilbertSymbol_comm _ b, hilbertSymbol_comm _ b']

theorem hs_one_left (b : Kv) : hs 1 b = 1 := by
  rw [hilbertSymbol_comm]; exact hilbertSymbol_one_right _ b

theorem hs_sq_mul (e : ℤ) (he : e = 1 ∨ e = -1) : e * e = 1 := by
  rcases he with rfl | rfl <;> norm_num

/-- **Nondegeneracy, element form:** a non-square $c \in F_v^\times$ has $(x, c)_v = -1$ for some $x \ne 0$. -/
theorem exists_hs_neg_one {c : Kv} (hc : c ≠ 0) (hsq : ¬ IsSquare c) : ∃ x : Kv, x ≠ 0 ∧ hs x c = -1 := by
  have hy : (QuotientGroup.mk (Units.mk0 c hc) : SqDual.SqCl Kv) ≠ 1 := by
    rw [Ne, SqDual.mk_eq_one_iff_isSquare]; exact hsq
  obtain ⟨x, hx⟩ := SqDual.hilbCl_nondeg_fin v _ hy
  induction x using QuotientGroup.induction_on with
  | H x => exact ⟨x, x.ne_zero, by simpa using hx⟩

/-- **Binary forms** (Serre IV §2.2): for $a, b, t \in F_v^\times$, $a X^2 + b Y^2 = t$ is solvable iff
$(t, -ab)_v = (a, b)_v$. -/
@[kb "serre1973" "Ch. IV §2.2, Thm. 6 (n = 2) [unverified]"]
theorem represents_two_iff {a b t : Kv} (ha : a ≠ 0) (hb : b ≠ 0) (ht : t ≠ 0) :
    (∃ X Y : Kv, a * X ^ 2 + b * Y ^ 2 = t) ↔ hs t (-(a * b)) = hs a b := by
  rw [HM4.binary_represents_iff Kv a b t ha hb ht]
  have hti : t⁻¹ ≠ 0 := inv_ne_zero ht
  have e1 : a / t = a * t * t⁻¹ ^ 2 := by field_simp
  have e2 : b / t = b * t * t⁻¹ ^ 2 := by field_simp
  have key : hs (a / t) (b / t) = hs a b * hs t (-(a * b)) := by
    rw [e1, e2, HN.hilbertSymbol_mul_sq_left _ _ _ _ hti, SqDual.hilbertSymbol_mul_sq_right _ _ _ _ hti,
      hs_mul_left v ha ht (mul_ne_zero hb ht), hs_mul_right v ha hb ht, hs_mul_right v ht hb ht]
    have htt : hs t t = hs t (-1) := by
      have h := hs_mul_right v ht (show (-1 : Kv) ≠ 0 by norm_num) (neg_ne_zero.2 ht)
      rw [show (-1 : Kv) * -t = t by ring, hilbertSymbol_self_neg, mul_one] at h
      exact h
    have hab : -(a * b) = a * b * -1 := by ring
    rw [htt, hab, hs_mul_right v ht (mul_ne_zero ha hb) (by norm_num), hs_mul_right v ht ha hb,
      hilbertSymbol_comm _ a t]
    ring
  rw [key]
  rcases hs_pm v a b with h | h <;> rcases hs_pm v t (-(a * b)) with h' | h' <;> simp [h, h']

/-! ### Two characters -/

/-- If $c_1$ and $c_1c_2$ are non-squares, some $g \ne 0$ has $(g, c_1) = -1$ and $(g, c_2) = 1$. -/
theorem exists_hs_neg_pos {c₁ c₂ : Kv} (h1 : c₁ ≠ 0) (h2 : c₂ ≠ 0) (hs1 : ¬ IsSquare c₁)
    (hs12 : ¬ IsSquare (c₁ * c₂)) : ∃ g : Kv, g ≠ 0 ∧ hs g c₁ = -1 ∧ hs g c₂ = 1 := by
  obtain ⟨x, hx0, hx⟩ := exists_hs_neg_one v h1 hs1
  obtain ⟨y, hy0, hy⟩ := exists_hs_neg_one v (mul_ne_zero h1 h2) hs12
  rw [hs_mul_right v hy0 h1 h2] at hy
  rcases hs_pm v x c₂ with hx2 | hx2
  · exact ⟨x, hx0, hx, hx2⟩
  rcases hs_pm v y c₁ with hy1 | hy1
  · -- `y = (1, -1)`: take `x * y`
    have hy2 : hs y c₂ = -1 := by rw [hy1, one_mul] at hy; exact hy
    refine ⟨x * y, mul_ne_zero hx0 hy0, ?_, ?_⟩
    · rw [hs_mul_left v hx0 hy0 h1, hx, hy1]; norm_num
    · rw [hs_mul_left v hx0 hy0 h2, hx2, hy2]; norm_num
  · have hy2 : hs y c₂ = 1 := by rw [hy1] at hy; linarith
    exact ⟨y, hy0, hy1, hy2⟩

/-- **Two independent characters:** if $c_1$, $c_2$ and $c_1c_2$ are non-squares in $F_v$, then for all signs $e_1, e_2$
some $t \ne 0$ has $(t, c_1)_v = e_1$ and $(t, c_2)_v = e_2$. -/
theorem exists_hs_eq_eq {c₁ c₂ : Kv} (h1 : c₁ ≠ 0) (h2 : c₂ ≠ 0) (hs1 : ¬ IsSquare c₁) (hs2 : ¬ IsSquare c₂)
    (hs12 : ¬ IsSquare (c₁ * c₂)) {e₁ e₂ : ℤ} (he₁ : e₁ = 1 ∨ e₁ = -1) (he₂ : e₂ = 1 ∨ e₂ = -1) :
    ∃ t : Kv, t ≠ 0 ∧ hs t c₁ = e₁ ∧ hs t c₂ = e₂ := by
  obtain ⟨g, hg0, hg1, hg2⟩ := exists_hs_neg_pos v h1 h2 hs1 hs12
  obtain ⟨g', hg0', hg2', hg1'⟩ := exists_hs_neg_pos v h2 h1 hs2 (by rwa [mul_comm])
  rcases he₁ with rfl | rfl <;> rcases he₂ with rfl | rfl
  · exact ⟨1, one_ne_zero, hs_one_left v _, hs_one_left v _⟩
  · exact ⟨g', hg0', hg1', hg2'⟩
  · exact ⟨g, hg0, hg1, hg2⟩
  · refine ⟨g * g', mul_ne_zero hg0 hg0', ?_, ?_⟩
    · rw [hs_mul_left v hg0 hg0' h1, hg1, hg1']; norm_num
    · rw [hs_mul_left v hg0 hg0' h2, hg2, hg2']; norm_num

/-! ### Diagonal forms -/

theorem evalIn_diag_four (b : Fin 4 → Kv) (x : Fin 4 → Kv) :
    (QuadForm.diag b).evalIn Kv x = b 0 * x 0 ^ 2 + b 1 * x 1 ^ 2 + b 2 * x 2 ^ 2 + b 3 * x 3 ^ 2 := by
  simp [QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_four, Matrix.diagonal]; ring

theorem evalIn_diag_five (b : Fin 5 → Kv) (x : Fin 5 → Kv) :
    (QuadForm.diag b).evalIn Kv x =
      b 0 * x 0 ^ 2 + b 1 * x 1 ^ 2 + b 2 * x 2 ^ 2 + b 3 * x 3 ^ 2 + b 4 * x 4 ^ 2 := by
  simp [QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_five, Matrix.diagonal]; ring

/-- **Quaternary forms with non-square determinant are isotropic over $F_v$** (Serre IV §2.2, Thm. 6, $n = 4$):
if $b_0, \dots, b_3 \in F_v^\times$ and $b_0b_1b_2b_3$ is not a square, $\langle b_0,b_1,b_2,b_3\rangle$ is isotropic. -/
@[kb "serre1973" "Ch. IV §2.2, Thm. 6 (n = 4) [unverified]"]
theorem isotropic_four_of_not_isSquare (b : Fin 4 → Kv) (hb : ∀ i, b i ≠ 0)
    (hd : ¬ IsSquare (b 0 * b 1 * b 2 * b 3)) : (QuadForm.diag b).IsotropicIn Kv := by
  have h0 := hb 0; have h1 := hb 1; have h2 := hb 2; have h3 := hb 3
  by_cases hA : IsSquare (-(b 0 * b 1))
  · obtain ⟨r, hr⟩ := hA
    refine ⟨![r, b 0, 0, 0], fun h => h0 (by simpa using congrFun h 1), ?_⟩
    rw [evalIn_diag_four]; simp; linear_combination (-(b 0)) * hr
  by_cases hB : IsSquare (-(b 2 * b 3))
  · obtain ⟨r, hr⟩ := hB
    refine ⟨![0, 0, r, b 2], fun h => h2 (by simpa using congrFun h 3), ?_⟩
    rw [evalIn_diag_four]; simp; linear_combination (-(b 2)) * hr
  have hc1 : -(b 0 * b 1) ≠ 0 := neg_ne_zero.2 (mul_ne_zero h0 h1)
  have hc2 : -(b 2 * b 3) ≠ 0 := neg_ne_zero.2 (mul_ne_zero h2 h3)
  have hC : ¬ IsSquare (-(b 0 * b 1) * -(b 2 * b 3)) := by
    have : -(b 0 * b 1) * -(b 2 * b 3) = b 0 * b 1 * b 2 * b 3 := by ring
    rwa [this]
  have he₂ : hs (b 2) (b 3) * hs (-1) (-(b 2 * b 3)) = 1 ∨ hs (b 2) (b 3) * hs (-1) (-(b 2 * b 3)) = -1 := by
    rcases hs_pm v (b 2) (b 3) with h | h <;> rcases hs_pm v (-1) (-(b 2 * b 3)) with h' | h' <;> simp [h, h']
  obtain ⟨t, ht0, ht1, ht2⟩ := exists_hs_eq_eq v hc1 hc2 hA hB hC (hs_pm v (b 0) (b 1)) he₂
  obtain ⟨X, Y, hXY⟩ := (represents_two_iff v h0 h1 ht0).2 ht1
  have hrep2 : hs (-t) (-(b 2 * b 3)) = hs (b 2) (b 3) := by
    have : -t = -1 * t := by ring
    rw [this, hs_mul_left v (by norm_num) ht0 hc2, ht2]
    rcases hs_pm v (-1) (-(b 2 * b 3)) with h | h <;> rw [h] <;> ring
  obtain ⟨Z, W, hZW⟩ := (represents_two_iff v h2 h3 (neg_ne_zero.2 ht0)).2 hrep2
  refine ⟨![X, Y, Z, W], fun h => ?_, ?_⟩
  · have hX : X = 0 := by simpa using congrFun h 0
    have hY : Y = 0 := by simpa using congrFun h 1
    apply ht0; rw [← hXY, hX, hY]; ring
  · rw [evalIn_diag_four]; simp; linear_combination hXY + hZW

/-- The square classes of $F_v$ number at least $4$. -/
theorem four_le_card_sqCl : 4 ≤ Nat.card (SqDual.SqCl Kv) := by
  have h := HN.index_sq_completion v
  rw [Subgroup.index] at h
  rw [h]
  have : 1 ≤ Ideal.absNorm v.asIdeal ^ HN.ordTwo v :=
    Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot))
  omega

/-- **A value of a binary form avoiding one square class:** if $-a_0a_1$ is not a square, then for every $c \ne 0$ some
$t \ne 0$ has $(t, -a_0a_1)_v = (a_0, a_1)_v$ (so $t$ is a value of $\langle a_0, a_1\rangle$) and $tc$ a non-square. -/
theorem exists_value_avoiding {a₀ a₁ c : Kv} (h0 : a₀ ≠ 0) (h1 : a₁ ≠ 0) (hc : c ≠ 0)
    (hA : ¬ IsSquare (-(a₀ * a₁))) :
    ∃ t : Kv, t ≠ 0 ∧ hs t (-(a₀ * a₁)) = hs a₀ a₁ ∧ ¬ IsSquare (t * c) := by
  classical
  set c₁ := -(a₀ * a₁) with hc₁
  have hc₁0 : c₁ ≠ 0 := neg_ne_zero.2 (mul_ne_zero h0 h1)
  set y : SqDual.SqCl Kv := QuotientGroup.mk (Units.mk0 c₁ hc₁0)
  set cc : SqDual.SqCl Kv := QuotientGroup.mk (Units.mk0 c hc)
  set ε := hs a₀ a₁
  by_contra hcon
  push Not at hcon
  -- every class `g` with `χ(g) = ε` is `cc⁻¹`
  have hR : ∀ g : SqDual.SqCl Kv, SqDual.hilbCl Kv g y = ε → g = cc⁻¹ := by
    intro g hg
    induction g using QuotientGroup.induction_on with
    | H t =>
    have hsq := hcon t t.ne_zero (by simpa [y] using hg)
    rw [eq_inv_iff_mul_eq_one, ← QuotientGroup.mk_mul, SqDual.mk_eq_one_iff_isSquare]
    simpa using hsq
  obtain ⟨x, hx0, hx⟩ := exists_hs_neg_one v hc₁0 hA
  set gx : SqDual.SqCl Kv := QuotientGroup.mk (Units.mk0 x hx0)
  have hgx : SqDual.hilbCl Kv gx y = -1 := by simpa [gx, y] using hx
  -- some class has value `ε`
  obtain ⟨r, hr⟩ : ∃ r : SqDual.SqCl Kv, SqDual.hilbCl Kv r y = ε := by
    rcases hs_pm v a₀ a₁ with h | h
    · refine ⟨1, ?_⟩
      rw [← QuotientGroup.mk_one, show y = QuotientGroup.mk (Units.mk0 c₁ hc₁0) from rfl, SqDual.hilbCl_mk]
      simp only [Units.val_one]; rw [hs_one_left, ← h]
    · exact ⟨gx, by rw [hgx, ← h]⟩
  have hall : ∀ g : SqDual.SqCl Kv, g = 1 ∨ g = gx⁻¹ := by
    intro g
    rcases SqDual.hilbCl_pm Kv g y with hg | hg
    · left
      have h1 : SqDual.hilbCl Kv (r * g) y = ε := by rw [SqDual.hilbCl_mul_fin, hr, hg, mul_one]
      have := (hR _ h1).trans (hR _ hr).symm
      have h' := congrArg (r⁻¹ * ·) (this.trans (mul_one r).symm); simpa using h'
    · right
      have h1 : SqDual.hilbCl Kv (g * gx) y = 1 := by rw [SqDual.hilbCl_mul_fin, hg, hgx]; norm_num
      rcases hs_pm v a₀ a₁ with hε | hε
      · have h2 : SqDual.hilbCl Kv (r * (g * gx)) y = ε := by rw [SqDual.hilbCl_mul_fin, hr, h1, mul_one]
        have := (hR _ h2).trans (hR _ hr).symm
        have h3 : g * gx = 1 := by
          have h' := congrArg (r⁻¹ * ·) (this.trans (mul_one r).symm); simpa using h'
        exact eq_inv_of_mul_eq_one_left h3
      · have h2 : SqDual.hilbCl Kv (r * (g * gx)) y = ε := by rw [SqDual.hilbCl_mul_fin, hr, h1, mul_one]
        have := (hR _ h2).trans (hR _ hr).symm
        have h3 : g * gx = 1 := by
          have h' := congrArg (r⁻¹ * ·) (this.trans (mul_one r).symm); simpa using h'
        exact eq_inv_of_mul_eq_one_left h3
  have hsurj : Function.Surjective (fun b : Bool => if b then (1 : SqDual.SqCl Kv) else gx⁻¹) := by
    intro g
    rcases hall g with h | h
    · exact ⟨true, by simp [h]⟩
    · exact ⟨false, by simp [h]⟩
  have hle := Nat.card_le_card_of_surjective _ hsurj
  have h4 : 4 ≤ Nat.card (SqDual.SqCl Kv) := four_le_card_sqCl v
  simp at hle
  omega

/-- **Diagonal forms of rank $5$ over $F_v$ are isotropic.** -/
@[kb "serre1973" "Ch. IV §2.2, Thm. 6, Cor. 2 [unverified]"]
theorem isotropic_diag_five (a : Fin 5 → Kv) (ha : ∀ i, a i ≠ 0) : (QuadForm.diag a).IsotropicIn Kv := by
  have h0 := ha 0; have h1 := ha 1; have h2 := ha 2; have h3 := ha 3; have h4 := ha 4
  by_cases hA : IsSquare (-(a 0 * a 1))
  · obtain ⟨r, hr⟩ := hA
    refine ⟨![r, a 0, 0, 0, 0], fun h => h0 (by simpa using congrFun h 1), ?_⟩
    rw [evalIn_diag_five]; simp; linear_combination (-(a 0)) * hr
  have hc : a 2 * a 3 * a 4 ≠ 0 := mul_ne_zero (mul_ne_zero h2 h3) h4
  obtain ⟨t, ht0, ht, hsq⟩ := exists_value_avoiding v h0 h1 hc hA
  obtain ⟨X, Y, hXY⟩ := (represents_two_iff v h0 h1 ht0).2 ht
  have hb : ∀ i, (![t, a 2, a 3, a 4] : Fin 4 → Kv) i ≠ 0 := by
    intro i; fin_cases i <;> simp [ht0, h2, h3, h4]
  have hd : ¬ IsSquare ((![t, a 2, a 3, a 4] : Fin 4 → Kv) 0 * (![t, a 2, a 3, a 4] : Fin 4 → Kv) 1 *
      (![t, a 2, a 3, a 4] : Fin 4 → Kv) 2 * (![t, a 2, a 3, a 4] : Fin 4 → Kv) 3) := by
    show ¬ IsSquare (t * a 2 * a 3 * a 4)
    rwa [show t * a 2 * a 3 * a 4 = t * (a 2 * a 3 * a 4) by ring]
  obtain ⟨z, hz0, hz⟩ := isotropic_four_of_not_isSquare v _ hb hd
  rw [evalIn_diag_four] at hz
  replace hz : t * z 0 ^ 2 + a 2 * z 1 ^ 2 + a 3 * z 2 ^ 2 + a 4 * z 3 ^ 2 = 0 := hz
  refine ⟨![X * z 0, Y * z 0, z 1, z 2, z 3], fun h => ?_, ?_⟩
  · have e1 : z 1 = 0 := by simpa using congrFun h 2
    have e2 : z 2 = 0 := by simpa using congrFun h 3
    have e3 : z 3 = 0 := by simpa using congrFun h 4
    have eX : X * z 0 = 0 := by simpa using congrFun h 0
    have eY : Y * z 0 = 0 := by simpa using congrFun h 1
    have e0 : z 0 = 0 := by
      by_contra hz0'
      apply ht0
      rw [← hXY, (mul_eq_zero.1 eX).resolve_right hz0', (mul_eq_zero.1 eY).resolve_right hz0']; ring
    apply hz0; funext i; fin_cases i <;> simp [e0, e1, e2, e3]
  · rw [evalIn_diag_five]; simp
    linear_combination z 0 ^ 2 * hXY + hz

/-- **Every nondegenerate form of rank $5$ over a non-archimedean completion $F_v$ is isotropic** (O'Meara 63:19;
Serre 1973, Ch. IV, §2.2, Thm. 6, Cor. 2 for $\mathbb Q_p$). -/
@[kb "serre1973" "Ch. IV §2.2, Thm. 6, Cor. 2 [unverified]"]
theorem isotropic_five (Q : QuadForm Kv 5) (hQ : Q.Nondegenerate) : Q.IsotropicIn Kv := by
  obtain ⟨a, ha, hiso⟩ := FieldGen.exists_isometric_diag Q hQ
  rw [FieldGen.isotropicIn_iff_of_isometricIn Kv hiso]
  exact isotropic_diag_five v a ha

end LocalRankFive

/-- **The input holds:** `Quat.LocalRankFiveIsotropic F` for every number field $F$. -/
@[kb "omeara1963" "63:19 [unverified]"]
theorem Quat.localRankFiveIsotropic (F : Type) [Field F] [NumberField F] : Quat.LocalRankFiveIsotropic F :=
  ⟨fun v Q hQ => LocalRankFive.isotropic_five v Q hQ⟩

namespace Quat

variable {F : Type} [Field F] [NumberField F]

/-- **The reduced norm is surjective at every finite place**, unconditionally: $\operatorname{nrd}(D_v^\times) = F_v^\times$. -/
@[kb "voight2021" "§13.4 [unverified]"]
theorem exists_nrd_eq_finite' {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) (v : HeightOneSpectrum (𝓞 F))
    {c : v.adicCompletion F} (hc : c ≠ 0) :
    ∃ y : ℍ[v.adicCompletion F, algebraMap F _ a, algebraMap F _ b], nrd y = c :=
  exists_nrd_eq_finite (localRankFiveIsotropic F) ha hb v hc

/-- **Every totally positive element is a reduced norm**, unconditionally. -/
@[kb "voight2021" "Thm. 14.7.4 [unverified]"]
theorem exists_nrd_eq_of_totallyPositive' {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) {c : F} (hc : c ≠ 0)
    (hpos : IsTotallyPositive c) : ∃ α : ℍ[F,a,b], IsUnit α ∧ nrd α = c :=
  exists_nrd_eq_of_totallyPositive (localRankFiveIsotropic F) ha hb hc hpos

/-- **Eichler's norm theorem** (totally definite case), **unconditional**: for $D = (a,b)_F$ totally definite over the
totally real field $F$, $\operatorname{nrd}(D^\times) = F^\times_+$. -/
@[kb "voight2021" "Thm. 14.7.4 [unverified]"]
theorem eichler_norm_theorem' {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) (hD : IsTotallyDefinite a b) (c : F) :
    (∃ α : ℍ[F,a,b], IsUnit α ∧ nrd α = c) ↔ c ≠ 0 ∧ IsTotallyPositive c :=
  eichler_norm_theorem (localRankFiveIsotropic F) ha hb hD c

end Quat

end QuadFormsKB
