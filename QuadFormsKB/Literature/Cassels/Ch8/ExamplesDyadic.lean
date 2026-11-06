/-
# Cassels, Chapter 8, Examples 3 (i)–(ii) and 4 (iii): forms over $\mathbb Z_2$

**Setting** (as in `Ch8/Dyadic.lean`): forms over $\mathbb Q_2$ by their symmetric matrices; $\mathbb Z_2$-equivalence
`ZpEquiv`; Cassels' blocks `DyBlock` and their orthogonal sums `dyMat`; improper primitivity `IsImproperlyPrimitive`.
Cassels' determinant $d(f)$ is the class of $\det F$ in $\mathbb Q_2^{\times}/(\mathbb Q_2^{\times})^{2}$, so
"$d(f) = 1$" is `IsSquare F.det`.

**Proves**
* `ex3_unit` (**Example 3 (i)**, p. 125): an improperly primitive form with unit determinant has an even number of
  variables and is $\mathbb Z_2$-equivalent to a sum of forms $2xy$ and $2x^{2} + 2xy + 2y^{2}$;
* `ex3_square` (**Example 3 (ii)**): if moreover $d(f) = 1$, then $4 \mid n$ and $f$ is a sum of forms $2xy$;
* `ex4_char_mod4` (**Example 4 (iii)**, p. 125): for a classically integral form over $\mathbb Z_2$ with unit
  determinant and a vector $\vec b$ as in Example 4 (i), $f(\vec b) \equiv n \pmod 2$ and
  $f(\vec b) - n \equiv d(f) - 1 \pmod 4$.
Example 3 (iii) and Example 4 (iv) (the Hasse–Minkowski invariant $c_2$) and Example 5 are not formalized.
-/
import QuadFormsKB.Literature.Cassels.Ch8.Dyadic
import QuadFormsKB.Literature.Cassels.Ch8.Examples

namespace QuadFormsKB.Cassels

open Matrix

variable {n : ℕ}

private theorem ed_c2 : (((2 : ℤ_[2])) : ℚ_[2]) = 2 := by norm_cast
private theorem ed_c3 : (((3 : ℤ_[2])) : ℚ_[2]) = 3 := by norm_cast
private theorem ed_c4 : (((4 : ℤ_[2])) : ℚ_[2]) = 4 := by norm_cast
private theorem ed_c6 : (((6 : ℤ_[2])) : ℚ_[2]) = 6 := by norm_cast
private theorem ed_c8 : (((8 : ℤ_[2])) : ℚ_[2]) = 8 := by norm_cast

/-- `4 ∣ n` in `ℤ₂` gives `4 ∣ n`. -/
private theorem ed_four_dvd_nat {n : ℕ} (h : (4 : ℤ_[2]) ∣ (n : ℤ_[2])) : 4 ∣ n := by
  have h4 : (2 : ℤ_[2]) ^ 2 ∣ (n : ℤ_[2]) := by rw [show (2 : ℤ_[2]) ^ 2 = 4 by norm_num]; exact h
  have hk : (n : ℤ_[2]) ∈ RingHom.ker (PadicInt.toZModPow (p := 2) 2) := by
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton]; simpa using h4
  rw [RingHom.mem_ker, map_natCast] at hk
  have := (ZMod.natCast_eq_zero_iff n (2 ^ 2)).1 hk
  simpa using this

/-- The square of a unit of `ℤ₂` is `1` mod `8`. -/
private theorem ed_sq_mod8 {w : ℤ_[2]} (hw : IsUnit w) : ∃ y : ℤ_[2], w ^ 2 = 1 + 8 * y := by
  obtain ⟨u₀, h0, t, ht⟩ := dyadic_exists_mod8 hw
  have hu : (u₀ : ℤ_[2]) ^ 2 = 1 + 8 * (((u₀ ^ 2 - 1) / 8 : ℤ) : ℤ_[2]) := by
    rcases h0 with rfl | rfl | rfl | rfl <;> norm_num
  have hw8 : w = u₀ + 8 * t := by
    have : w = u₀ + (2 : ℤ_[2]) ^ 3 * t := by rw [← ht]; ring
    rw [this]; norm_num
  refine ⟨(((u₀ ^ 2 - 1) / 8 : ℤ) + 2 * u₀ * t + 8 * t ^ 2 : ℤ_[2]), ?_⟩
  rw [hw8, add_sq]; rw [hu]; ring

/-- Even unimodular: `2 ∣ n` and `det ≡ 1 - n (mod 4)`. -/
private theorem ed_EU_det : ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) ℚ_[2]), dyadicEU G →
    2 ∣ n ∧ ∃ z : ℤ_[2], G.det = 1 - (n : ℚ_[2]) + 4 * (z : ℚ_[2]) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G hG
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · refine ⟨by simp, 0, ?_⟩
      simp
    · exact (dyadic_EU_fin_one hG).elim
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 + m := ⟨n - 2, by omega⟩
  obtain ⟨X, E', hX, hE', hz⟩ := dyadic_EU_split hG
  obtain ⟨hm2, z', hz'⟩ := ih m (by omega) E' hE'
  obtain ⟨k, hk⟩ := hm2
  obtain ⟨s, hs, hdet⟩ := dyadic_zpEquiv_det_rel hz.symm
  obtain ⟨w, u₀, rfl, hw, -, -⟩ := dyadic_exists_lift hs
  obtain ⟨y, hy⟩ := ed_sq_mod8 hw
  have hy' : ((w : ℚ_[2])) ^ 2 = 1 + 8 * (y : ℚ_[2]) := by
    have := congrArg (fun x : ℤ_[2] => (x : ℚ_[2])) hy
    simpa [ed_c8] using this
  rw [dyadic_det_orthSumMat] at hdet
  refine ⟨by omega, ?_⟩
  have hmq : (m : ℚ_[2]) = 2 * k := by rw [hk]; push_cast; ring
  rcases hX with rfl | rfl
  · rw [Matrix.det_fin_two_of] at hdet
    refine ⟨(k : ℤ_[2]) - z' - 2 * y * (1 - 2 * k + 4 * z'), ?_⟩
    rw [hdet, hy', hz']
    push_cast [ed_c2, ed_c3, ed_c4, ed_c6, ed_c8]
    rw [hmq]; ring
  · rw [Matrix.det_fin_two_of] at hdet
    refine ⟨1 - (k : ℤ_[2]) + 3 * z' + 6 * y * (1 - 2 * k + 4 * z'), ?_⟩
    rw [hdet, hy', hz']
    push_cast [ed_c2, ed_c3, ed_c4, ed_c6, ed_c8]
    rw [hmq]; ring


private theorem ed_mat_hyp : (DyBlock.hyp 0).mat = (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ_[2]) := by
  show (2 : ℚ_[2]) ^ (0 : ℤ) • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ_[2]) = _
  simp

private theorem ed_mat_ell : (DyBlock.ell 0).mat = (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℚ_[2]) := by
  show (2 : ℚ_[2]) ^ (0 : ℤ) • (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℚ_[2]) = _
  simp

/-- Even unimodular matrices are sums of `hyp 0` and `ell 0` blocks. -/
private theorem ed_ex3_aux : ∀ (n : ℕ) (F : Matrix (Fin n) (Fin n) ℚ_[2]), dyadicEU F →
    2 ∣ n ∧ ∃ D : List DyBlock, (∀ b ∈ D, b = .hyp 0 ∨ b = .ell 0) ∧ ∃ h : dyDim D = n,
      ZpEquiv F ((dyMat D).submatrix (Fin.cast h.symm) (Fin.cast h.symm)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F hF
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · refine ⟨by simp, [], by simp, rfl, ?_⟩
      convert ZpEquiv.refl F using 1; exact Subsingleton.elim _ _
    · exact (dyadic_EU_fin_one hF).elim
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 + m := ⟨n - 2, by omega⟩
  obtain ⟨X, E', hX, hE', hz⟩ := dyadic_EU_split hF
  obtain ⟨hm2, D', hD', h', hE⟩ := ih m (by omega) E' hE'
  subst h'
  refine ⟨by omega, ?_⟩
  rcases hX with rfl | rfl
  · have hFE : ZpEquiv F (orthSumMat (DyBlock.hyp 0).mat (dyMat D')) := by
      rw [ed_mat_hyp]; exact hz.trans (dyadic_zpEquiv_orthSum (ZpEquiv.refl _) hE)
    refine ⟨.hyp 0 :: D', ?_, rfl, hFE⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Or.inl rfl
    · exact hD' x hx
  · have hFE : ZpEquiv F (orthSumMat (DyBlock.ell 0).mat (dyMat D')) := by
      rw [ed_mat_ell]; exact hz.trans (dyadic_zpEquiv_orthSum (ZpEquiv.refl _) hE)
    refine ⟨.ell 0 :: D', ?_, rfl, hFE⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Or.inr rfl
    · exact hD' x hx

private theorem ed_dyadicEU_of_improper {F : Matrix (Fin n) (Fin n) ℚ_[2]} (hF : Fᵀ = F)
    (hFi : IsImproperlyPrimitive F) (hu : ‖F.det‖ = 1) : dyadicEU F :=
  ⟨hF, hFi.1.1, fun i => lt_of_le_of_ne (hFi.1.1 i i) (fun hi => hFi.2 ⟨hFi.1, i, hi⟩), hu⟩

private theorem ed_EU_cast {n n' : ℕ} (h : n = n') {G : Matrix (Fin n') (Fin n') ℚ_[2]} (hG : dyadicEU G) :
    dyadicEU (G.submatrix (Fin.cast h) (Fin.cast h)) ∧ (G.submatrix (Fin.cast h) (Fin.cast h)).det = G.det := by
  subst h
  exact ⟨hG, rfl⟩

private theorem ed_EU_hyp_block : dyadicEU (DyBlock.hyp 0).mat := by
  show dyadicEU ((2 : ℚ_[2]) ^ (0 : ℤ) • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ_[2]))
  rw [zpow_zero, one_smul]; exact dyadic_EU_H

private theorem ed_det_hyp_block : (DyBlock.hyp 0).mat.det = -1 := by
  show Matrix.det ((2 : ℚ_[2]) ^ (0 : ℤ) • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ_[2])) = -1
  rw [zpow_zero, one_smul]; simp [Matrix.det_fin_two_of]

private theorem ed_EU_hyp : ∀ D : List DyBlock, (∀ b ∈ D, b = .hyp 0) →
    dyadicEU (dyMat D) ∧ (dyMat D).det = (-1) ^ D.length
  | [], _ => by
    show dyadicEU (0 : Matrix (Fin 0) (Fin 0) ℚ_[2]) ∧ (0 : Matrix (Fin 0) (Fin 0) ℚ_[2]).det = 1
    refine ⟨⟨Subsingleton.elim _ _, fun i => i.elim0, fun i => i.elim0, ?_⟩, ?_⟩
    · simp
    · simp
  | b :: D, hD => by
    have hb : b = .hyp 0 := hD b (List.mem_cons_self)
    subst hb
    obtain ⟨h1, h2⟩ := ed_EU_hyp D (fun x hx => hD x (List.mem_cons_of_mem _ hx))
    refine ⟨dyadic_EU_orthSum ed_EU_hyp_block h1, ?_⟩
    have := dyadic_det_orthSumMat (DyBlock.hyp 0).mat (dyMat D)
    show (orthSumMat (DyBlock.hyp 0).mat (dyMat D)).det = _
    rw [this, ed_det_hyp_block, h2, List.length_cons, pow_succ]; ring

private theorem ed_dyDim_replicate (k : ℕ) : dyDim (List.replicate k (DyBlock.hyp 0)) = 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show 2 + dyDim (List.replicate k (DyBlock.hyp 0)) = _
    rw [ih]; ring

/-- Divisibility by $2$ in $\mathbb Z_2$ is vanishing of the reduction mod $2$. -/
private theorem ed_two_dvd_iff_toZMod (x : ℤ_[2]) : (2 : ℤ_[2]) ∣ x ↔ PadicInt.toZMod x = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
  simp

/-- Over $\mathbb F_2$, $\vec a^{t}G\vec a = \sum_i G_{ii}a_i$ for symmetric $G$. -/
private theorem ed_zmod_two_quad (G : Matrix (Fin n) (Fin n) (ZMod 2)) (hG : Gᵀ = G) (a : Fin n → ZMod 2) :
    a ⬝ᵥ (G *ᵥ a) = ∑ i, G i i * a i := by
  have hsymm : ∀ i j, G j i = G i j := fun i j => by
    have := congrFun (congrFun hG i) j
    simpa [Matrix.transpose_apply] using this
  set f : Fin n × Fin n → ZMod 2 := fun x => if x.1 = x.2 then 0 else a x.1 * G x.1 x.2 * a x.2 with hf
  have h0 : ∑ x, f x = 0 := by
    refine Finset.sum_involution (fun x _ => (x.2, x.1)) ?_ ?_ ?_ ?_
    · intro x _
      by_cases h : x.1 = x.2
      · simp [hf, h]
      · have h' : x.2 ≠ x.1 := fun e => h e.symm
        simp only [hf, h, h', ite_false, hsymm x.1 x.2]
        have : ∀ y : ZMod 2, y + y = 0 := by decide
        rw [show a x.2 * G x.1 x.2 * a x.1 = a x.1 * G x.1 x.2 * a x.2 by ring]
        exact this _
    · intro x _ hx h
      apply hx
      have : x.2 = x.1 := congrArg Prod.fst h
      simp [hf, this]
    · intros; exact Finset.mem_univ _
    · intro x _; rfl
  have h1 : a ⬝ᵥ (G *ᵥ a) = ∑ x : Fin n × Fin n, a x.1 * G x.1 x.2 * a x.2 := by
    simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have h2 : ∀ x : Fin n × Fin n, a x.1 * G x.1 x.2 * a x.2 = f x + if x.1 = x.2 then G x.1 x.1 * a x.1 else 0 := by
    intro x
    by_cases h : x.1 = x.2
    · have sq : ∀ y : ZMod 2, y * y = y := by decide
      simp only [hf, h, ite_true, zero_add]
      rw [← h]
      linear_combination (G x.1 x.1) * sq (a x.1)
    · simp [hf, h]
  rw [h1, Finset.sum_congr rfl fun x _ => h2 x, Finset.sum_add_distrib, h0, zero_add, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

/-- For symmetric $F$ over $\mathbb Z_2$, $\vec a^{t}F\vec a - \sum_i F_{ii}a_i$ is even. -/
private theorem ed_two_dvd_quad_diag (F : Matrix (Fin n) (Fin n) ℤ_[2]) (hF : Fᵀ = F) (a : Fin n → ℤ_[2]) :
    (2 : ℤ_[2]) ∣ a ⬝ᵥ (F *ᵥ a) - a ⬝ᵥ (fun i => F i i) := by
  rw [ed_two_dvd_iff_toZMod, map_sub, sub_eq_zero]
  have hG : (F.map (PadicInt.toZMod : ℤ_[2] →+* ZMod 2))ᵀ = F.map (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) := by
    rw [← Matrix.transpose_map, hF]
  have := ed_zmod_two_quad _ hG (fun i => PadicInt.toZMod (a i))
  have h1 : PadicInt.toZMod (a ⬝ᵥ (F *ᵥ a)) = (fun i => PadicInt.toZMod (a i)) ⬝ᵥ
      ((F.map (PadicInt.toZMod : ℤ_[2] →+* ZMod 2)) *ᵥ (fun i => PadicInt.toZMod (a i))) := by
    simp [dotProduct, Matrix.mulVec, map_sum, map_mul, Matrix.map_apply]
  rw [h1, this]
  simp [dotProduct, map_sum, map_mul, Matrix.map_apply, mul_comm]

private theorem ed_unit_sub_one {x : ℤ_[2]} (hx : IsUnit x) : (2 : ℤ_[2]) ∣ x - 1 := by
  rw [ed_two_dvd_iff_toZMod, map_sub, map_one, sub_eq_zero]
  by_contra h
  have h0 : PadicInt.toZMod x = 0 := by
    have : ∀ z : ZMod 2, z ≠ 1 → z = 0 := by decide
    exact this _ h
  exact dyadic_not_isUnit_of_two_dvd ((ed_two_dvd_iff_toZMod x).2 h0) hx

private theorem ed_arith (u β d f m : ℤ_[2]) (hu : (2 : ℤ_[2]) ∣ u - 1) (hβ : (2 : ℤ_[2]) ∣ 1 - β)
    (hd : (2 : ℤ_[2]) ∣ d - 1) (H1 : (2 : ℤ_[2]) ∣ f - m) (H2 : (4 : ℤ_[2]) ∣ (f - m) - (d - 1)) :
    (2 : ℤ_[2]) ∣ (β * u * β + f) - (1 + m) ∧ (4 : ℤ_[2]) ∣ ((β * u * β + f) - (1 + m)) - (u * d - 1) := by
  obtain ⟨p, hp⟩ := hu
  obtain ⟨q, hq⟩ := hβ
  obtain ⟨r, hr⟩ := hd
  obtain ⟨s, hs⟩ := H1
  obtain ⟨t, ht⟩ := H2
  have eu : u = 1 + 2 * p := by linear_combination hp
  have eb : β = 1 - 2 * q := by linear_combination -hq
  have ed : d = 1 + 2 * r := by linear_combination hr
  have ef : f = m + 2 * s := by linear_combination hs
  subst eu eb ed ef
  refine ⟨⟨-2 * q + 2 * q ^ 2 + p - 4 * p * q + 4 * p * q ^ 2 + s, by ring⟩,
    ⟨(1 + 2 * p) * (q ^ 2 - q) + t - p * r, ?_⟩⟩
  linear_combination ht

private theorem ed_bd {P Q : Type} [Fintype P] [Fintype Q] [DecidableEq P] [DecidableEq Q]
    (A : Matrix P P ℤ_[2]) (S : Matrix Q Q ℤ_[2]) (x1 y1 : P → ℤ_[2]) (x2 y2 : Q → ℤ_[2]) :
    Sum.elim x1 x2 ⬝ᵥ (fromBlocks A 0 0 S *ᵥ Sum.elim y1 y2) = x1 ⬝ᵥ (A *ᵥ y1) + x2 ⬝ᵥ (S *ᵥ y2) := by
  rw [Matrix.fromBlocks_mulVec]
  simp [dotProduct, Fintype.sum_sum_type]

private theorem ed_uq {P : Type} [Fintype P] [Unique P] (A : Matrix P P ℤ_[2]) (x y : P → ℤ_[2]) :
    x ⬝ᵥ (A *ᵥ y) = x default * A default default * y default := by
  simp [dotProduct, Matrix.mulVec]
  ring

private theorem ed_blocks {P Q : Type} [Fintype P] [DecidableEq P] [Unique P] [Fintype Q] [DecidableEq Q]
    (A : Matrix P P ℤ_[2]) (S : Matrix Q Q ℤ_[2]) (hu : IsUnit (A default default)) (hS : IsUnit S.det)
    (IH : ∀ b2 : Q → ℤ_[2], (∀ a, (2 : ℤ_[2]) ∣ a ⬝ᵥ (S *ᵥ a) - a ⬝ᵥ (S *ᵥ b2)) →
      (2 : ℤ_[2]) ∣ b2 ⬝ᵥ (S *ᵥ b2) - (Fintype.card Q : ℕ) ∧
        (4 : ℤ_[2]) ∣ (b2 ⬝ᵥ (S *ᵥ b2) - (Fintype.card Q : ℕ)) - (S.det - 1))
    (c : P ⊕ Q → ℤ_[2])
    (hc : ∀ a, (2 : ℤ_[2]) ∣ a ⬝ᵥ (fromBlocks A 0 0 S *ᵥ a) - a ⬝ᵥ (fromBlocks A 0 0 S *ᵥ c)) :
    (2 : ℤ_[2]) ∣ c ⬝ᵥ (fromBlocks A 0 0 S *ᵥ c) - (Fintype.card (P ⊕ Q) : ℕ) ∧
      (4 : ℤ_[2]) ∣ (c ⬝ᵥ (fromBlocks A 0 0 S *ᵥ c) - (Fintype.card (P ⊕ Q) : ℕ)) -
        ((fromBlocks A 0 0 S).det - 1) := by
  obtain ⟨c1, c2, rfl⟩ : ∃ (c1 : P → ℤ_[2]) (c2 : Q → ℤ_[2]), c = Sum.elim c1 c2 :=
    ⟨c ∘ Sum.inl, c ∘ Sum.inr, (Sum.elim_comp_inl_inr c).symm⟩
  have hc' : ∀ a1 a2, (2 : ℤ_[2]) ∣ (a1 ⬝ᵥ (A *ᵥ a1) + a2 ⬝ᵥ (S *ᵥ a2)) -
      (a1 ⬝ᵥ (A *ᵥ c1) + a2 ⬝ᵥ (S *ᵥ c2)) := by
    intro a1 a2
    have := hc (Sum.elim a1 a2)
    rwa [ed_bd, ed_bd] at this
  have hS' : ∀ a2, (2 : ℤ_[2]) ∣ a2 ⬝ᵥ (S *ᵥ a2) - a2 ⬝ᵥ (S *ᵥ c2) := by
    intro a2
    have := hc' 0 a2
    simpa using this
  have hA : (2 : ℤ_[2]) ∣ 1 - c1 default := by
    have h1 := hc' (fun _ => 1) 0
    simp only [ed_uq, Matrix.mulVec_zero, dotProduct_zero, zero_dotProduct, add_zero] at h1
    have h2 : (2 : ℤ_[2]) ∣ A default default * (1 - c1 default) := by
      convert h1 using 1; ring
    exact (hu.dvd_mul_left).1 h2
  obtain ⟨H1, H2⟩ := IH c2 hS'
  have e : ((Fintype.card (P ⊕ Q) : ℕ) : ℤ_[2]) = 1 + ((Fintype.card Q : ℕ) : ℤ_[2]) := by
    rw [Fintype.card_sum, Fintype.card_unique]; push_cast; ring
  have hdet : (fromBlocks A 0 0 S).det = A default default * S.det := by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_unique]
  rw [ed_bd, ed_uq, e, hdet]
  exact ed_arith _ _ _ _ _ (ed_unit_sub_one hu) hA (ed_unit_sub_one hS) H1 H2

private theorem ed_two_dvd_of_not_unit {x : ℤ_[2]} (hx : ¬ IsUnit x) : (2 : ℤ_[2]) ∣ x := by
  by_contra h
  apply hx
  rw [PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt => h ?_)
  simpa using (PadicInt.norm_lt_one_iff_dvd (p := 2) x).1 hlt

private theorem ed_case2 {n : ℕ} (F : Matrix (Fin n) (Fin n) ℤ_[2]) (hF : Fᵀ = F) (hd : IsUnit F.det)
    (hdiag : ∀ i, (2 : ℤ_[2]) ∣ F i i) {b : Fin n → ℤ_[2]}
    (hb : ∀ a, (2 : ℤ_[2]) ∣ a ⬝ᵥ (F *ᵥ a) - a ⬝ᵥ (F *ᵥ b)) :
    (2 : ℤ_[2]) ∣ b ⬝ᵥ (F *ᵥ b) - n ∧ (4 : ℤ_[2]) ∣ (b ⬝ᵥ (F *ᵥ b) - n) - (F.det - 1) := by
  have hEU : dyadicEU (F.map PadicInt.Coe.ringHom) := by
    refine ⟨by rw [← Matrix.transpose_map, hF], fun i j => PadicInt.norm_le_one _, fun i => ?_, ?_⟩
    · have := (PadicInt.norm_lt_one_iff_dvd (p := 2) (F i i)).2 (by simpa using hdiag i)
      simpa using this
    · rw [dyadic_det_map_coe]
      have := PadicInt.isUnit_iff.1 hd
      rwa [PadicInt.norm_def] at this
  obtain ⟨⟨k, hk⟩, z, hz⟩ := ed_EU_det n _ hEU
  rw [dyadic_det_map_coe] at hz
  have hz' : F.det = 1 - (n : ℤ_[2]) + 4 * z := by
    apply PadicInt.ext
    rw [hz]; push_cast [ed_c4]; ring
  have hb0 : ∀ a, (2 : ℤ_[2]) ∣ a ⬝ᵥ (F *ᵥ a) - a ⬝ᵥ (F *ᵥ (0 : Fin n → ℤ_[2])) := by
    intro a
    rw [Matrix.mulVec_zero, dotProduct_zero, sub_zero]
    have h := ed_two_dvd_quad_diag F hF a
    have h2 : (2 : ℤ_[2]) ∣ a ⬝ᵥ (fun i => F i i) :=
      Finset.dvd_sum fun i _ => Dvd.dvd.mul_left (hdiag i) _
    simpa using dvd_add h h2
  have hev : ∀ i, (2 : ℤ_[2]) ∣ b i := fun i => by simpa using ex4_char_unique F hF hd hb hb0 i
  choose c hc using hev
  have hbc : b = (2 : ℤ_[2]) • c := funext fun i => by simp [hc i]
  have hq : b ⬝ᵥ (F *ᵥ b) = 4 * (c ⬝ᵥ (F *ᵥ c)) := by
    rw [hbc]; simp [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]; ring
  rw [hq, hz']
  refine ⟨⟨2 * (c ⬝ᵥ (F *ᵥ c)) - k, ?_⟩, ⟨c ⬝ᵥ (F *ᵥ c) - z, ?_⟩⟩
  · have hn : (n : ℤ_[2]) = 2 * k := by exact_mod_cast hk
    linear_combination -hn
  · ring

private theorem ed_re_quad {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ)
    (F : Matrix ι ι ℤ_[2]) (x y : κ → ℤ_[2]) :
    x ⬝ᵥ (F.submatrix e.symm e.symm *ᵥ y) = (x ∘ e) ⬝ᵥ (F *ᵥ (y ∘ e)) := by
  rw [Matrix.submatrix_mulVec_equiv, Equiv.symm_symm]
  simp only [dotProduct]
  rw [← Equiv.sum_comp e]
  simp

private theorem ed_re_char {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ)
    (F : Matrix ι ι ℤ_[2]) (b : ι → ℤ_[2]) (hb : ∀ a, (2 : ℤ_[2]) ∣ a ⬝ᵥ (F *ᵥ a) - a ⬝ᵥ (F *ᵥ b)) :
    ∀ a', (2 : ℤ_[2]) ∣ a' ⬝ᵥ (F.submatrix e.symm e.symm *ᵥ a') -
      a' ⬝ᵥ (F.submatrix e.symm e.symm *ᵥ (b ∘ e.symm)) := by
  intro a'
  rw [ed_re_quad, ed_re_quad]
  have := hb (a' ∘ e)
  have hb' : (b ∘ e.symm) ∘ e = b := by funext i; simp
  rwa [hb']

private theorem ed_re_concl {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ)
    (F : Matrix ι ι ℤ_[2]) (b : ι → ℤ_[2]) (m : ℕ)
    (H : (2 : ℤ_[2]) ∣ (b ∘ e.symm) ⬝ᵥ (F.submatrix e.symm e.symm *ᵥ (b ∘ e.symm)) - m ∧
      (4 : ℤ_[2]) ∣ ((b ∘ e.symm) ⬝ᵥ (F.submatrix e.symm e.symm *ᵥ (b ∘ e.symm)) - m) -
        ((F.submatrix e.symm e.symm).det - 1)) :
    (2 : ℤ_[2]) ∣ b ⬝ᵥ (F *ᵥ b) - m ∧ (4 : ℤ_[2]) ∣ (b ⬝ᵥ (F *ᵥ b) - m) - (F.det - 1) := by
  have h1 : (b ∘ e.symm) ⬝ᵥ (F.submatrix e.symm e.symm *ᵥ (b ∘ e.symm)) = b ⬝ᵥ (F *ᵥ b) := by
    rw [ed_re_quad]
    have : (b ∘ e.symm) ∘ e = b := by funext i; simp
    rw [this]
  rw [h1, Matrix.det_submatrix_equiv_self] at H
  exact H

private theorem ed_nopivot {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ} (hk : Fintype.card ι = k)
    (F : Matrix ι ι ℤ_[2]) (hF : Fᵀ = F) (hd : IsUnit F.det) (hdiag : ∀ i, (2 : ℤ_[2]) ∣ F i i)
    (b : ι → ℤ_[2]) (hb : ∀ a, (2 : ℤ_[2]) ∣ a ⬝ᵥ (F *ᵥ a) - a ⬝ᵥ (F *ᵥ b)) :
    (2 : ℤ_[2]) ∣ b ⬝ᵥ (F *ᵥ b) - (k : ℕ) ∧ (4 : ℤ_[2]) ∣ (b ⬝ᵥ (F *ᵥ b) - (k : ℕ)) - (F.det - 1) := by
  let e : ι ≃ Fin k := (Fintype.equivFin ι).trans (finCongr hk)
  refine ed_re_concl e F b k ?_
  exact ed_case2 (F.submatrix e.symm e.symm) (by rw [Matrix.transpose_submatrix, hF])
    (by rw [Matrix.det_submatrix_equiv_self]; exact hd) (fun i => hdiag _) (ed_re_char e F b hb)

private theorem ed_cong_quad {κ : Type} [Fintype κ] [DecidableEq κ] (T N : Matrix κ κ ℤ_[2]) (x y : κ → ℤ_[2]) :
    x ⬝ᵥ ((Tᵀ * N * T) *ᵥ y) = (T *ᵥ x) ⬝ᵥ (N *ᵥ (T *ᵥ y)) := by
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

private theorem ed_pivot {P Q : Type} [Fintype P] [DecidableEq P] [Unique P] [Fintype Q] [DecidableEq Q]
    (M : Matrix (P ⊕ Q) (P ⊕ Q) ℤ_[2]) (hM : Mᵀ = M) (hdet : IsUnit M.det)
    (hu : IsUnit (M (Sum.inl default) (Sum.inl default)))
    (IH : ∀ S : Matrix Q Q ℤ_[2], Sᵀ = S → IsUnit S.det → ∀ b2 : Q → ℤ_[2],
      (∀ a, (2 : ℤ_[2]) ∣ a ⬝ᵥ (S *ᵥ a) - a ⬝ᵥ (S *ᵥ b2)) →
      (2 : ℤ_[2]) ∣ b2 ⬝ᵥ (S *ᵥ b2) - (Fintype.card Q : ℕ) ∧
        (4 : ℤ_[2]) ∣ (b2 ⬝ᵥ (S *ᵥ b2) - (Fintype.card Q : ℕ)) - (S.det - 1))
    (b : P ⊕ Q → ℤ_[2]) (hb : ∀ a, (2 : ℤ_[2]) ∣ a ⬝ᵥ (M *ᵥ a) - a ⬝ᵥ (M *ᵥ b)) :
    (2 : ℤ_[2]) ∣ b ⬝ᵥ (M *ᵥ b) - (Fintype.card (P ⊕ Q) : ℕ) ∧
      (4 : ℤ_[2]) ∣ (b ⬝ᵥ (M *ᵥ b) - (Fintype.card (P ⊕ Q) : ℕ)) - (M.det - 1) := by
  obtain ⟨A, B, C, D, rfl⟩ : ∃ (A : Matrix P P ℤ_[2]) (B : Matrix P Q ℤ_[2]) (C : Matrix Q P ℤ_[2])
      (D : Matrix Q Q ℤ_[2]), M = fromBlocks A B C D :=
    ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks M).symm⟩
  rw [Matrix.fromBlocks_transpose] at hM
  obtain ⟨hA, hCB, hBC, hD⟩ := Matrix.fromBlocks_inj.1 hM
  have hu' : IsUnit (A default default) := by simpa using hu
  have hAdet : IsUnit A.det := by rw [Matrix.det_unique]; exact hu'
  let _ : Invertible A := Matrix.invertibleOfIsUnitDet A hAdet
  have hAinv : (⅟A)ᵀ = ⅟A := by rw [Matrix.invOf_eq_nonsing_inv, Matrix.transpose_nonsing_inv, hA]
  set S := D - C * ⅟A * B with hSdef
  set T : Matrix (P ⊕ Q) (P ⊕ Q) ℤ_[2] := fromBlocks 1 (⅟A * B) 0 1 with hT
  have hTt : Tᵀ = fromBlocks 1 0 (C * ⅟A) 1 := by
    rw [hT, Matrix.fromBlocks_transpose]
    simp [Matrix.transpose_mul, hBC]
  have hfac : fromBlocks A B C D = Tᵀ * fromBlocks A 0 0 S * T := by
    rw [hTt]; exact Matrix.fromBlocks_eq_of_invertible₁₁ A B C D
  have hSsym : Sᵀ = S := by
    simp only [hSdef, Matrix.transpose_sub, Matrix.transpose_mul, hAinv, hBC, hCB, hD, Matrix.mul_assoc]
  have hTdet : T.det = 1 := by rw [hT, Matrix.det_fromBlocks_zero₂₁]; simp
  have hNdet : (fromBlocks A 0 0 S).det = A.det * S.det := Matrix.det_fromBlocks_zero₂₁ _ _ _
  have hMdet : (fromBlocks A B C D).det = (fromBlocks A 0 0 S).det := by
    rw [hfac, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hTdet]; ring
  have hSdet : IsUnit S.det := by
    rw [hMdet, hNdet] at hdet
    exact (IsUnit.mul_iff.1 hdet).2
  have hTinv : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv T (by rw [hTdet]; exact isUnit_one)
  have hchar : ∀ a', (2 : ℤ_[2]) ∣ a' ⬝ᵥ (fromBlocks A 0 0 S *ᵥ a') -
      a' ⬝ᵥ (fromBlocks A 0 0 S *ᵥ (T *ᵥ b)) := by
    intro a'
    have := hb (T⁻¹ *ᵥ a')
    have hTa : T *ᵥ (T⁻¹ *ᵥ a') = a' := by rw [Matrix.mulVec_mulVec, hTinv, Matrix.one_mulVec]
    rw [hfac, ed_cong_quad, ed_cong_quad, hTa] at this
    exact this
  obtain ⟨h1, h2⟩ := ed_blocks A S hu' hSdet (IH S hSsym hSdet) (T *ᵥ b) hchar
  have hv : b ⬝ᵥ (fromBlocks A B C D *ᵥ b) = (T *ᵥ b) ⬝ᵥ (fromBlocks A 0 0 S *ᵥ (T *ᵥ b)) := by
    rw [hfac, ed_cong_quad]
  rw [hv, hMdet]
  exact ⟨h1, h2⟩

private theorem ed_main : ∀ (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = k →
    ∀ (F : Matrix ι ι ℤ_[2]), Fᵀ = F → IsUnit F.det → ∀ b : ι → ℤ_[2],
      (∀ a, (2 : ℤ_[2]) ∣ a ⬝ᵥ (F *ᵥ a) - a ⬝ᵥ (F *ᵥ b)) →
      (2 : ℤ_[2]) ∣ b ⬝ᵥ (F *ᵥ b) - (k : ℕ) ∧ (4 : ℤ_[2]) ∣ (b ⬝ᵥ (F *ᵥ b) - (k : ℕ)) - (F.det - 1) := by
  intro k
  induction k with
  | zero =>
    intro ι _ _ hk F hF hd b hb
    exact ed_nopivot hk F hF hd (fun i => ((Fintype.card_eq_zero_iff.1 hk).false i).elim) b hb
  | succ k ih =>
    intro ι _ _ hk F hF hd b hb
    by_cases hpiv : ∃ i, IsUnit (F i i)
    · obtain ⟨i, hi⟩ := hpiv
      let _ : Unique {x : ι // x = i} := { default := ⟨i, rfl⟩, uniq := fun x => Subtype.ext x.2 }
      let e : ι ≃ {x : ι // x = i} ⊕ {x : ι // ¬ x = i} := (Equiv.sumCompl (fun x => x = i)).symm
      have hcard : Fintype.card ({x : ι // x = i} ⊕ {x : ι // ¬ x = i}) = k + 1 := by
        rw [← Fintype.card_congr e]; exact hk
      have hcardQ : Fintype.card {x : ι // ¬ x = i} = k := by
        rw [Fintype.card_sum, Fintype.card_unique] at hcard; omega
      refine ed_re_concl e F b (k + 1) ?_
      have := ed_pivot (F.submatrix e.symm e.symm) (by rw [Matrix.transpose_submatrix, hF])
        (by rw [Matrix.det_submatrix_equiv_self]; exact hd) (by show IsUnit (F i i); exact hi)
        (fun S hS hdS b2 hb2 => by simpa only [hcardQ] using ih {x : ι // ¬ x = i} hcardQ S hS hdS b2 hb2)
        (b ∘ e.symm) (ed_re_char e F b hb)
      rwa [hcard] at this
    · push Not at hpiv
      exact ed_nopivot hk F hF hd (fun i => ed_two_dvd_of_not_unit (hpiv i)) b hb



/-- **Cassels, Ch. 8, Example 3 (i)**: *let $f$ be an improperly primitive $\mathbb Z_2$-form in $n$ variables. If
$d(f)$ is a unit then $2 \mid n$ and $f$ is $\mathbb Z_2$-equivalent to a sum of forms $2xy$ or
$2x^{2} + 2xy + 2y^{2}$.* (Blocks `hyp 0` and `ell 0`.) -/
@[kb "cassels1978" "Ch. 8, Ex. 3 (i), p. 125"]
theorem ex3_unit {F : Matrix (Fin n) (Fin n) ℚ_[2]} (hF : Fᵀ = F) (hFi : IsImproperlyPrimitive F)
    (hu : ‖F.det‖ = 1) :
    2 ∣ n ∧ ∃ D : List DyBlock, (∀ b ∈ D, b = .hyp 0 ∨ b = .ell 0) ∧ ∃ h : dyDim D = n,
      ZpEquiv F ((dyMat D).submatrix (Fin.cast h.symm) (Fin.cast h.symm)) := by
  exact ed_ex3_aux n F (ed_dyadicEU_of_improper hF hFi hu)

/-- **Cassels, Ch. 8, Example 3 (ii)**: *if $d(f) = 1$, then $4 \mid n$ and $f$ is $\mathbb Z_2$-equivalent to a sum of
forms $2xy$.* Here $d(f) = 1$ in $\mathbb Q_2^{\times}/(\mathbb Q_2^{\times})^{2}$ (`IsSquare F.det`), and $f$ is
improperly primitive (which, with a square determinant, forces $d(f)$ to be a unit only up to squares; we assume
$\lvert d(f)\rvert = 1$ as in (i)). -/
@[kb "cassels1978" "Ch. 8, Ex. 3 (ii), p. 125"]
theorem ex3_square {F : Matrix (Fin n) (Fin n) ℚ_[2]} (hF : Fᵀ = F) (hFi : IsImproperlyPrimitive F)
    (hu : ‖F.det‖ = 1) (hsq : IsSquare F.det) :
    4 ∣ n ∧ ∃ D : List DyBlock, (∀ b ∈ D, b = .hyp 0) ∧ ∃ h : dyDim D = n,
      ZpEquiv F ((dyMat D).submatrix (Fin.cast h.symm) (Fin.cast h.symm)) := by
  have hEF := ed_dyadicEU_of_improper hF hFi hu
  obtain ⟨-, z, hz⟩ := ed_EU_det n F hEF
  obtain ⟨r, hr⟩ := hsq
  have hr1 : ‖r‖ = 1 := by
    have h1 : ‖r‖ * ‖r‖ = 1 := by rw [← norm_mul, ← hr]; exact hu
    have h0 : 0 ≤ ‖r‖ := norm_nonneg r
    nlinarith
  have hr0 : r ≠ 0 := fun h0 => by rw [h0, norm_zero] at hr1; exact zero_ne_one hr1
  have h4 : 4 ∣ n := by
    obtain ⟨w, u₀, hwr, hw, -, -⟩ := dyadic_exists_lift hr1
    obtain ⟨y, hy⟩ := ed_sq_mod8 hw
    have hy' : ((w : ℚ_[2])) ^ 2 = 1 + 8 * (y : ℚ_[2]) := by
      have := congrArg (fun x : ℤ_[2] => (x : ℚ_[2])) hy
      simpa [ed_c8] using this
    have e1 : F.det = 1 + 8 * (y : ℚ_[2]) := by rw [hr, ← hwr, ← pow_two, hy']
    apply ed_four_dvd_nat
    refine ⟨z - 2 * y, PadicInt.ext ?_⟩
    push_cast [ed_c2, ed_c4, ed_c8]
    linear_combination hz - e1
  obtain ⟨j, hj⟩ := h4
  set D : List DyBlock := List.replicate (2 * j) (DyBlock.hyp 0) with hDdef
  have hDh : ∀ b ∈ D, b = DyBlock.hyp 0 := fun b hb => List.eq_of_mem_replicate hb
  have hdim : dyDim D = n := by rw [hDdef, ed_dyDim_replicate]; omega
  obtain ⟨hEG, hdetG⟩ := ed_EU_hyp D hDh
  obtain ⟨hEG', hdetG'⟩ := ed_EU_cast hdim.symm hEG
  refine ⟨⟨j, hj⟩, D, hDh, hdim, ?_⟩
  refine dyadic_EU_equiv n F _ hEF hEG' ⟨r⁻¹, by rw [norm_inv, hr1]; simp, ?_⟩
  rw [hdetG', hdetG, hr, hDdef, List.length_replicate]
  field_simp
  rw [pow_mul]; simp


/-- **Cassels, Ch. 8, Example 4 (iii)**: *let $f$ be a classically integral $\mathbb Z_2$-form in $n$ variables with
$d(f)$ a unit and $\vec b$ as in (i). Show that $f(\vec b) \equiv n \pmod 2$ and that
$f(\vec b) - n \equiv d(f) - 1 \pmod 4$.* -/
@[kb "cassels1978" "Ch. 8, Ex. 4 (iii), p. 125"]
theorem ex4_char_mod4 (F : Matrix (Fin n) (Fin n) ℤ_[2]) (hF : Fᵀ = F) (hd : IsUnit F.det)
    {b : Fin n → ℤ_[2]} (hb : ∀ a, (2 : ℤ_[2]) ∣ a ⬝ᵥ (F *ᵥ a) - a ⬝ᵥ (F *ᵥ b)) :
    (2 : ℤ_[2]) ∣ b ⬝ᵥ (F *ᵥ b) - n ∧ (4 : ℤ_[2]) ∣ (b ⬝ᵥ (F *ᵥ b) - n) - (F.det - 1) := by
  exact ed_main n (Fin n) (Fintype.card_fin n) F hF hd b hb

end QuadFormsKB.Cassels
