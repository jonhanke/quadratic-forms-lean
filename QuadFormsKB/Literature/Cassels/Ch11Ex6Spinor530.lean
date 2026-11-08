/-
# Cassels, Chapter 11, Example 6: the $2$-adic spinor norm bound for $x^2 + y^2 + 16z^2$

For the form $f = x_0^2 + x_1^2 + 16x_2^2$ (Gram matrix $A_6 = \mathrm{diag}(1, 1, 16)$, `csQ A6`) and a place $v$ of
$\mathbb Q$ over $2$, every $2$-adically automorphous number of $\mathbb Z_2^3$ lies in the subgroup
$$H = \langle 2, 5\rangle\,\mathbb Q_2^{\times 2}/\mathbb Q_2^{\times 2} = \{1, 2, 5, 10\}$$
of square classes (`H6`), which is the group of norms from $\mathbb Q_2(i)$ (`theta2_le_A6_gen`). The proof follows
Conway–Sloane §11 (`theta2_le_A11_gen`): an automorph moves $e_2$ (the Jordan constituent of scale $16$) only by a
multiple of $16$ in the first two coordinates, so $\sigma e_2 = (16a, 16b, c)$ with $c \equiv \pm1 \pmod 8$; after
composing with the symmetry in $e_2$ (spinor norm $16$, a square) we may take $c = 1 - 8t$, whence
$t(1 - 4t) = a^2 + b^2$ and $Q(e_2 - \sigma e_2) = 256\,t$; the symmetry in $e_2 - \sigma e_2$ maps $\sigma e_2$ back to
$e_2$, and the rest is an isometry of the binary space $e_2^\perp = \langle 1, 1\rangle$ whose spinor norms are norms
$x^2 + y^2$ (Wall's formula, `spinorNorm_mem_H6_of_fix`), lying in $H$ (`normH6`).
-/
import QuadFormsKB.Literature.ConwaySloane.Section11TwoClasses
import QuadFormsKB.Literature.Cassels.Ch11Examples4

open NumberField IsDedekindDomain WithZero Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices Ex11 Wall EvenUnimodular

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

/-- The Gram matrix $A_6 = \mathrm{diag}(1, 1, 16)$ of $f = x_0^2 + x_1^2 + 16x_2^2$ (Cassels, Ch. 11, Example 6). -/
def A6 : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 0; 0, 1, 0; 0, 0, 16]

/-- $A_6$ is symmetric. -/
theorem A6_symm : A6ᵀ = A6 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- $\det A_6 = 16$. -/
theorem A6_det : A6.det = 16 := by
  simp [A6, Matrix.det_fin_three]

/-- The Hessian of the form of $A_6$ is $\mathrm{diag}(2, 2, 32)$. -/
theorem A6_hessian : (Cassels.Ch8Ex2.gramForm A6).hessian = !![2, 0, 0; 0, 2, 0; 0, 0, 32] := by
  rw [hessian_csForm A6_symm]
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- The rational form of $A_6$ is nondegenerate. -/
theorem A6_nondeg : (csQ A6).Nondegenerate := csQ_nondegenerate A6_symm (by rw [A6_det]; norm_num)

section Two

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "F2" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

/-- The subgroup $H = \langle 2, 5\rangle \mathbb Q_v^{\times 2}/\mathbb Q_v^{\times 2} = \{1, 2, 5, 10\}$ of square
classes (for $v \mid 2$ the norms from $\mathbb Q_2(i)$). Argument `v`: the place. -/
def H6 (v : HeightOneSpectrum (𝓞 ℚ)) : Subgroup (SqClass (v.adicCompletion ℚ)) :=
  Subgroup.closure {sqClassOf (2 : v.adicCompletion ℚ), sqClassOf (5 : v.adicCompletion ℚ)}

theorem two_mem_H6 : sqClassOf (2 : F2) ∈ H6 v := Subgroup.subset_closure (by simp)

theorem five_mem_H6 : sqClassOf (5 : F2) ∈ H6 v := Subgroup.subset_closure (by simp)

/-- A nonzero element equal to $d s^2$ with $d \in \{1, 2, 5, 10\}$ has its square class in $H$. -/
theorem mem_H6_of_eq {z d s : F2} (hd : d = 1 ∨ d = 2 ∨ d = 5 ∨ d = 10) (hs : s ≠ 0) (h : z = d * s ^ 2) :
    sqClassOf z ∈ H6 v := by
  have hd0 : d ≠ 0 := by rcases hd with rfl | rfl | rfl | rfl <;> norm_num
  have hz : z = s ^ 2 * d := by rw [h]; ring
  rw [hz, sqClassOf_sq_mul hs hd0]
  rcases hd with rfl | rfl | rfl | rfl
  · rw [sqClassOf_one]; exact (H6 v).one_mem
  · exact two_mem_H6
  · exact five_mem_H6
  · rw [show (10 : F2) = 2 * 5 by norm_num, sqClassOf_mul (by norm_num) (by norm_num)]
    exact (H6 v).mul_mem two_mem_H6 five_mem_H6

/-- $1 + 4t$ is $1$ or $5$ times a square, for $t \in \mathbb Z_2$. -/
theorem onePlusFour (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (t : 𝔬) :
    ∃ d s : F2, (d = 1 ∨ d = 5) ∧ s ≠ 0 ∧ 1 + 4 * (t : F2) = d * s ^ 2 := by
  rcases isUnit_or_two_dvd h2 t with ht | ⟨m, rfl⟩
  · rcases isUnit_or_two_dvd h2 (t - 1) with h | ⟨k, hk⟩
    · exact absurd h ((IsLocalRing.mem_maximalIdeal _).mp (sub_mem_max h2 ht isUnit_one))
    · have h5 : IsUnit (5 : 𝔬) := by
        have := (Rl.natCast (v := v) 5).od_unit h2 (by decide)
        simpa using this
      obtain ⟨s, hs, e⟩ := cong_sq h2 h5 k (x := 1 + 4 * t) (by linear_combination 4 * hk)
      refine ⟨5, (s : F2), Or.inr rfl, fun h0 => hs.ne_zero (Subtype.ext h0), ?_⟩
      have := congrArg (fun z : 𝔬 => (z : F2)) e
      push_cast at this
      rw [show ((4 : 𝔬) : F2) = 4 from map_ofNat (𝔬).subtype 4, show ((5 : 𝔬) : F2) = 5 from map_ofNat (𝔬).subtype 5]
        at this
      exact this
  · obtain ⟨s, hs⟩ := exists_sq_one_add_eight h2 m
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact one_ne_two_mul h2 (-(4 * m)) (by linear_combination -hs)
    refine ⟨1, (s : F2), Or.inl rfl, fun h0 => hs0 (Subtype.ext h0), ?_⟩
    have := congrArg (fun z : 𝔬 => (z : F2)) hs
    push_cast at this
    rw [show ((8 : 𝔬) : F2) = 8 from map_ofNat (𝔬).subtype 8] at this
    rw [one_mul]
    have h4 : (s : F2) ^ 2 = 1 + 8 * (m : F2) := this
    rw [h4]
    show 1 + 4 * ((2 * m : 𝔬) : F2) = _
    push_cast
    rw [show ((2 : 𝔬) : F2) = 2 from map_ofNat (𝔬).subtype 2]
    ring

/-- For $b \in \mathbb Z_2$, $1 + b^2$ is $d s^2$ with $d \in \{1, 2, 5, 10\}$. -/
theorem onePlusSq (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (b : 𝔬) :
    ∃ d s : F2, (d = 1 ∨ d = 2 ∨ d = 5 ∨ d = 10) ∧ s ≠ 0 ∧ 1 + (b : F2) ^ 2 = d * s ^ 2 := by
  rcases isUnit_or_two_dvd h2 b with hb | ⟨c, rfl⟩
  · obtain ⟨m, hm⟩ := exists_sq_eq_of_isUnit h2 hb
    obtain ⟨d, s, hd, hs, e⟩ := onePlusFour h2 m
    refine ⟨2 * d, s, ?_, hs, ?_⟩
    · rcases hd with rfl | rfl
      · exact Or.inr (Or.inl (by norm_num))
      · exact Or.inr (Or.inr (Or.inr (by norm_num)))
    · have := congrArg (fun z : 𝔬 => (z : F2)) hm
      push_cast at this
      rw [show ((8 : 𝔬) : F2) = 8 from map_ofNat (𝔬).subtype 8] at this
      have e2 : (b : F2) ^ 2 = 1 + 8 * (m : F2) := this
      calc 1 + (b : F2) ^ 2 = 2 * (1 + 4 * (m : F2)) := by rw [e2]; ring
        _ = 2 * d * s ^ 2 := by rw [e]; ring
  · obtain ⟨d, s, hd, hs, e⟩ := onePlusFour h2 (c ^ 2)
    refine ⟨d, s, ?_, hs, ?_⟩
    · rcases hd with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
    · push_cast at e ⊢
      rw [show ((2 : 𝔬) : F2) = 2 from map_ofNat (𝔬).subtype 2]
      rw [← e]; ring

/-- **The norms $x^2 + y^2$ from $\mathbb Q_2(i)$ lie in $H$.** -/
theorem normH6_aux (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (x y : F2) (hxy : Valued.v y ≤ Valued.v x) (h : x ^ 2 + y ^ 2 ≠ 0) :
    sqClassOf (x ^ 2 + y ^ 2) ∈ H6 v := by
  have hx : x ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hxy
    have hy0 : y = 0 := (Valuation.zero_iff _).mp (le_antisymm hxy zero_le)
    apply h; rw [h0, hy0]; ring
  have hb : Valued.v (y / x) ≤ 1 := by
    rw [map_div₀, div_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hx))]; exact hxy
  obtain ⟨d, s, hd, hs, e⟩ := onePlusSq h2 (toOel (y / x) hb)
  refine mem_H6_of_eq (d := d) (s := x * s) hd (mul_ne_zero hx hs) ?_
  have e' : 1 + (y / x) ^ 2 = d * s ^ 2 := e
  calc x ^ 2 + y ^ 2 = x ^ 2 * (1 + (y / x) ^ 2) := by field_simp
    _ = d * (x * s) ^ 2 := by rw [e']; ring

/-- **The norms $x^2 + y^2$ from $\mathbb Q_2(i)$ lie in $H$.** -/
theorem normH6 (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (x y : F2) (h : x ^ 2 + y ^ 2 ≠ 0) :
    sqClassOf (x ^ 2 + y ^ 2) ∈ H6 v := by
  by_cases hxy : Valued.v y ≤ Valued.v x
  · exact normH6_aux h2 x y hxy h
  · have := normH6_aux h2 y x (le_of_not_ge hxy) (by rwa [add_comm])
    rwa [add_comm] at this

theorem hess_A6 : (csQ A6).hessian.map (algebraMap ℚ F2) = Matrix.diagonal ![2, 2, 32] := by
  rw [hessian_csQ_map A6_symm]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.diagonal_apply, A6, smul_eq_mul] <;> push_cast <;>
    norm_num

theorem csQ_A6_eval (x : Fin 3 → F2) :
    (csQ A6).evalIn F2 x = x 0 ^ 2 + x 1 ^ 2 + 16 * x 2 ^ 2 := by
  have h := two_mul_evalIn_locGram (Q := csQ A6) (v := v) 1 x
  simp only [Units.val_one, one_mulVec] at h
  have hG : ∀ k l, locGram (csQ A6) v 1 k l = (((Cassels.Ch8Ex2.gramForm A6).hessian k l : ℤ) : F2) :=
    fun k l => locGram_one_int v _ k l
  rw [dotProduct, Fin.sum_univ_three] at h
  simp only [mulVec, dotProduct, Fin.sum_univ_three, hG, A6_hessian] at h
  norm_num at h
  have h2 : (2 : F2) ≠ 0 := two_ne_zero
  apply mul_left_cancel₀ h2
  rw [h]; ring

/-- $-1$ is not a square in $\mathbb Q_2$: $x^2 + y^2 = 0$ forces $x = y = 0$. -/
theorem eq_zero_of_sq_add_sq (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {x y : F2} (h : x ^ 2 + y ^ 2 = 0) : x = 0 ∧ y = 0 := by
  by_contra hne
  have hy : y ≠ 0 ∨ x ≠ 0 := by
    by_contra hh; push Not at hh; exact hne ⟨hh.2, hh.1⟩
  have key : ∀ x y : F2, Valued.v y ≤ Valued.v x → x ^ 2 + y ^ 2 = 0 → x = 0 := by
    intro x y hxy h
    by_contra hx
    have hb : Valued.v (y / x) ≤ 1 := by
      rw [map_div₀, div_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hx))]; exact hxy
    obtain ⟨d, s, hd, hs, e⟩ := onePlusSq h2 (toOel (y / x) hb)
    have e' : 1 + (y / x) ^ 2 = d * s ^ 2 := e
    have h1 : 1 + (y / x) ^ 2 = 0 := by
      have : x ^ 2 * (1 + (y / x) ^ 2) = 0 := by
        calc x ^ 2 * (1 + (y / x) ^ 2) = x ^ 2 + y ^ 2 := by field_simp
          _ = 0 := h
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h') hx
      · exact h'
    rw [e'] at h1
    have hd0 : d ≠ 0 := by rcases hd with rfl | rfl | rfl | rfl <;> norm_num
    exact mul_ne_zero hd0 (pow_ne_zero 2 hs) h1
  by_cases hxy : Valued.v y ≤ Valued.v x
  · have hx := key x y hxy h
    rw [hx] at h
    have : y ^ 2 = 0 := by linear_combination h
    have hy0 := pow_eq_zero_iff (by norm_num) |>.mp this
    exact hne ⟨hx, hy0⟩
  · have hy := key y x (le_of_not_ge hxy) (by rw [add_comm]; exact h)
    rw [hy] at h
    have : x ^ 2 = 0 := by linear_combination h
    have hx0 := pow_eq_zero_iff (by norm_num) |>.mp this
    exact hne ⟨hx0, hy⟩

/-- **Isometries fixing $e_2$ have spinor norms in $H$** (Wall's formula on the binary space
$e_2^\perp = \langle 1, 1\rangle$). Arguments: `h2` ($v \mid 2$), `ρ` the isometry, `hρ` ($\rho e_2 = e_2$). -/
theorem spinorNorm_mem_H6_of_fix (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (ρ : orthGroup (csQ A6) F2)
    (hρ : mat (csQ A6) F2 ρ *ᵥ Pi.single 2 1 = Pi.single 2 1) : spinorNorm (csQ A6) F2 ρ ∈ H6 v := by
  obtain ⟨m, P, R, hf⟩ := exists_wallFrame (mat (csQ A6) F2 ρ)
  obtain ⟨hθ, hne, -⟩ := wall_formula A6_nondeg ρ hf
  rw [hθ]
  have hTR := hf.1
  have hcol : ∀ j, (fun k => P k j) = (1 - mat (csQ A6) F2 ρ) *ᵥ (fun k => R k j) := fun j => by
    ext k; rw [← mul_apply_col, hTR]
  have hP2 : ∀ j, P 2 j = 0 := by
    intro j
    have h := orth_ker ρ (fun k => R k j) _ hρ
    rw [← hcol j, hess_A6] at h
    simp [Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_three, Pi.single_apply] at h
    exact h
  have hm : m ≤ 2 := by
    set P' : Matrix (Fin 2) (Fin m) F2 := Matrix.of fun i j => ![P 0 j, P 1 j] i
    have hinj : Function.Injective (Matrix.toLin' P') := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro c hc
      apply hf.2.1 c
      have hc' : P' *ᵥ c = 0 := by simpa using hc
      have h0 : (P *ᵥ c) 0 = 0 := congrFun hc' 0
      have h1 : (P *ᵥ c) 1 = 0 := congrFun hc' 1
      have h2' : (P *ᵥ c) 2 = 0 := by
        show ∑ j, P 2 j * c j = 0
        simp [hP2]
      funext k
      fin_cases k
      · exact h0
      · exact h1
      · exact h2'
    have := LinearMap.finrank_le_finrank_of_injective hinj
    simpa using this
  have hdiag : ∀ j, (wallGram (csQ A6) F2 P R) j j = (csQ A6).evalIn F2 (fun k => P k j) := by
    intro j
    rw [wallGram, Wall.gram_apply, hcol j]
    exact wall_diag ρ _
  have hQP : ∀ j, (csQ A6).evalIn F2 (fun k => P k j) = P 0 j ^ 2 + P 1 j ^ 2 := by
    intro j; rw [csQ_A6_eval]; simp [hP2]
  interval_cases m
  · rw [Matrix.det_isEmpty, sqClassOf_one]
    exact (H6 v).one_mem
  · rw [Matrix.det_unique, show (default : Fin 1) = 0 from rfl, hdiag, hQP]
    have hne' : P 0 0 ^ 2 + P 1 0 ^ 2 ≠ 0 := by
      intro h0; apply hne; rw [Matrix.det_unique, show (default : Fin 1) = 0 from rfl, hdiag, hQP, h0]
    exact normH6 h2 _ _ hne'
  · have hsym := wall_symm_id (G := (csQ A6).hessian.map (algebraMap ℚ F2))
      (by rw [hess_A6]; simp) (mat_orth ρ) hTR
    have h01 : wallGram (csQ A6) F2 P R 0 1 + wallGram (csQ A6) F2 P R 1 0 =
        2 * (P 0 0 * P 0 1 + P 1 0 * P 1 1) := by
      have := congrFun (congrFun hsym 0) 1
      rw [Matrix.add_apply, transpose_apply] at this
      change wallGram (csQ A6) F2 P R 0 1 + wallGram (csQ A6) F2 P R 1 0 = _ at this
      rw [this, Wall.gram_apply, hess_A6]
      simp [Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_three, hP2]
      ring
    set C := wallGram (csQ A6) F2 P R
    have e : C.det = (C 0 1 - (P 0 0 * P 0 1 + P 1 0 * P 1 1)) ^ 2 +
        (P 0 0 * P 1 1 - P 1 0 * P 0 1) ^ 2 := by
      rw [Matrix.det_fin_two, hdiag, hdiag, hQP, hQP]
      have hC10 : C 1 0 = 2 * (P 0 0 * P 0 1 + P 1 0 * P 1 1) - C 0 1 := by
        linear_combination h01
      rw [hC10]; ring
    rw [e] at hne ⊢
    exact normH6 h2 _ _ hne

/-- The key step: an isometry $\sigma$ with $\sigma e_2 = (16a, 16b, c)$, $a, b$ integral and $c \equiv 1 \pmod 8$,
has spinor norm in $H$. Arguments: `σ`, `a b c`, `ha hb` (integrality), `hs` (the image of $e_2$), `hc`
($\lvert c - 1\rvert \le 2^{-3}$ in the normalization $\lvert 2\rvert = 2^{-1}$). -/
theorem spinorNorm_mem_H6_key (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (σ : orthGroup (csQ A6) F2) {a b c : F2}
    (ha : Valued.v a ≤ 1) (hb : Valued.v b ≤ 1)
    (hs : mat (csQ A6) F2 σ *ᵥ Pi.single 2 1 = ![16 * a, 16 * b, c])
    (hc : Valued.v (c - 1) ≤ exp (-3 : ℤ)) : spinorNorm (csQ A6) F2 σ ∈ H6 v := by
  have h2v : Valued.v (2 : F2) = exp (-1 : ℤ) :=
    valued_two_of_primeOf ((two_mem_iff_natGenerator v).mp h2)
  set e2 : Fin 3 → F2 := Pi.single 2 1
  have hQe2 : (csQ A6).evalIn F2 e2 = 16 := by
    rw [csQ_A6_eval]; simp [e2, Pi.single_apply]
  have hQs : (csQ A6).evalIn F2 (mat (csQ A6) F2 σ *ᵥ e2) = 16 := by
    rw [evalIn_mulVec_of_mem (csQ A6) σ.2, hQe2]
  have hQs' := hQs
  rw [hs, csQ_A6_eval] at hQs
  change (16 * a) ^ 2 + (16 * b) ^ 2 + 16 * c ^ 2 = 16 at hQs
  have hrel : c ^ 2 = 1 - 16 * (a ^ 2 + b ^ 2) := by linear_combination hQs / 16
  set t : F2 := (1 - c) / 8 with ht
  have h8 : Valued.v (8 : F2) = exp (-3 : ℤ) := by
    rw [show (8 : F2) = 2 ^ 3 by norm_num, map_pow, h2v, ← WithZero.exp_nsmul]; norm_num
  have ht1 : Valued.v t ≤ 1 := by
    rw [ht, map_div₀, h8, div_le_one₀ (zero_lt_iff.mpr exp_ne_zero), ← Valuation.map_neg, neg_sub]
    exact hc
  have htrel : t * (1 - 4 * t) = a ^ 2 + b ^ 2 := by
    rw [ht]; linear_combination (-1 / 16 : F2) * hrel
  by_cases ht0 : t = 0
  · -- `σ e₂ = e₂`
    have hc1 : c = 1 := by
      have : (1 - c) / 8 = 0 := ht0
      field_simp at this; linear_combination -this
    rw [ht0, zero_mul] at htrel
    obtain ⟨ha0, hb0⟩ := eq_zero_of_sq_add_sq h2 (x := a) (y := b) (by linear_combination -htrel)
    refine spinorNorm_mem_H6_of_fix h2 σ ?_
    rw [hs, ha0, hb0, hc1]
    ext k; fin_cases k <;> simp [Pi.single_apply]
  · set s' := mat (csQ A6) F2 σ *ᵥ e2
    have hs' : s' = ![16 * a, 16 * b, c] := hs
    set x := e2 - s'
    have hxv : x = ![-(16 * a), -(16 * b), 1 - c] := by
      ext k; fin_cases k <;> simp [x, hs', e2, Pi.single_apply, Matrix.vecHead, Matrix.vecTail] <;> ring
    have hQx : (csQ A6).evalIn F2 x = 256 * t := by
      rw [csQ_A6_eval, hxv]
      change (-(16 * a)) ^ 2 + (-(16 * b)) ^ 2 + 16 * (1 - c) ^ 2 = 256 * t
      rw [ht]
      linear_combination (16 : F2) * hrel
    have h1t : (1 - 4 * t) ≠ 0 := by
      intro h0
      have : Valued.v (1 - 4 * t) = 1 := by
        rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_left]
        · simp
        · rw [Valuation.map_neg, map_one, map_mul]
          have h4 : Valued.v (4 : F2) < 1 := by
            rw [show (4 : F2) = 2 ^ 2 by norm_num, map_pow, h2v, ← WithZero.exp_nsmul, ← exp_zero, exp_lt_exp]
            norm_num
          exact Levels.lt_one_of_lt_le h4 ht1
      rw [h0, map_zero] at this; exact zero_ne_one this
    have hQx0 : (csQ A6).evalIn F2 x ≠ 0 := by rw [hQx]; exact mul_ne_zero (by norm_num) ht0
    have hτ : mat (csQ A6) F2 (symm (csQ A6) F2 x) *ᵥ s' = e2 :=
      symm_sub_apply (csQ A6) F2 (x := e2) (y := s') (by rw [hQe2, hQs']) hQx0
    set ρ := symm (csQ A6) F2 x * σ
    have hρ : mat (csQ A6) F2 ρ *ᵥ e2 = e2 := by
      rw [mat_mul, ← mulVec_mulVec]; exact hτ
    have hθρ := spinorNorm_mem_H6_of_fix h2 ρ hρ
    have hσρ : σ = symm (csQ A6) F2 x * ρ := by
      simp only [ρ, ← mul_assoc, symm_mul_self, one_mul]
    have hmul : spinorNorm (csQ A6) F2 σ =
        spinorNorm (csQ A6) F2 (symm (csQ A6) F2 x) * spinorNorm (csQ A6) F2 ρ := by
      conv_lhs => rw [hσρ]
      exact (spinorNormHom (csQ A6) F2 A6_nondeg).map_mul _ _
    rw [hmul, spinorNorm_symm (csQ A6) F2 A6_nondeg hQx0, hQx]
    refine (H6 v).mul_mem ?_ hθρ
    -- `256 t = 16² · t`, and `t (1 - 4t) = a² + b²` with `1 - 4t` of class `1` or `5`
    have hnorm : a ^ 2 + b ^ 2 ≠ 0 := by rw [← htrel]; exact mul_ne_zero ht0 h1t
    have e1' : (256 : F2) * t = (16 : F2) ^ 2 * t := by ring
    rw [e1', sqClassOf_sq_mul (by norm_num) ht0]
    obtain ⟨d, s, hd, hs0, hds⟩ := onePlusFour h2 (toOel (-t) (by rw [Valuation.map_neg]; exact ht1))
    have hds' : 1 - 4 * t = d * s ^ 2 := by
      have : 1 + 4 * ((toOel (-t) (by rw [Valuation.map_neg]; exact ht1) : 𝔬) : F2) = d * s ^ 2 := hds
      rw [← this]; change 1 - 4 * t = 1 + 4 * (-t); ring
    have hd0 : d ≠ 0 := by rcases hd with rfl | rfl <;> norm_num
    have hdcls : sqClassOf d ∈ H6 v := by
      rcases hd with rfl | rfl
      · rw [sqClassOf_one]; exact (H6 v).one_mem
      · exact five_mem_H6
    have hmulc : sqClassOf (a ^ 2 + b ^ 2) = sqClassOf t * sqClassOf d := by
      have : a ^ 2 + b ^ 2 = s ^ 2 * (t * d) := by rw [← htrel, hds']; ring
      rw [this, sqClassOf_sq_mul hs0 (mul_ne_zero ht0 hd0), sqClassOf_mul ht0 hd0]
    have : sqClassOf t = sqClassOf (a ^ 2 + b ^ 2) * (sqClassOf d)⁻¹ := by
      rw [hmulc, mul_inv_cancel_right]
    rw [this]
    exact (H6 v).mul_mem (normH6 h2 a b hnorm) ((H6 v).inv_mem hdcls)

/-- **The $2$-adically automorphous numbers of $f = x_0^2 + x_1^2 + 16x_2^2$ lie in $H = \{1, 2, 5, 10\}$**
(unconditional; at any place $v \mid 2$). Arguments: `h2` ($v \mid 2$), `A` the unit of $\mathbb Q_v$, `hA` ($A \in
\theta(\mathbb Z_v^3)$). -/
theorem theta2_le_A6_gen (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (A : F2ˣ)
    (hA : A ∈ localSpinorNormGroup (csQ A6) A6_nondeg v stdLat) : SqClass.mk A ∈ H6 v := by
  have h2v : Valued.v (2 : F2) = exp (-1 : ℤ) :=
    valued_two_of_primeOf ((two_mem_iff_natGenerator v).mp h2)
  obtain ⟨σ, ⟨hσL, -⟩, hσB⟩ := (mem_localSpinorNormGroup (csQ A6) A6_nondeg v stdLat).mp hA
  rw [← hσB]
  have hdA : A6.det ≠ 0 := by rw [A6_det]; norm_num
  have hSi := entries_le_one_of_mem_locStabV A6_symm hdA ((locStabV (csQ A6) v stdLat).inv_mem hσL)
  set S := mat (csQ A6) F2 σ
  set Si := mat (csQ A6) F2 σ⁻¹
  have hSSi : S * Si = 1 := by
    rw [← mat_mul, mul_inv_cancel]; rfl
  have hH := hess_A6 (v := v)
  have hrow : Sᵀ * Matrix.diagonal ![2, 2, 32] = Matrix.diagonal ![2, 2, 32] * Si := by
    have h := mat_orth σ
    rw [hH] at h
    calc Sᵀ * Matrix.diagonal ![2, 2, 32] = Sᵀ * Matrix.diagonal ![2, 2, 32] * (S * Si) := by
          rw [hSSi, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h]
  have h20 := congrFun (congrFun hrow 2) 0
  have h21 := congrFun (congrFun hrow 2) 1
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, transpose_apply] at h20 h21
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h20 h21
  set a := Si 2 0
  set b := Si 2 1
  set c := S 2 2
  have ha : Valued.v a ≤ 1 := hSi 2 0
  have hb : Valued.v b ≤ 1 := hSi 2 1
  have e0 : S 0 2 = 16 * a := by linear_combination h20 / 2
  have e1 : S 1 2 = 16 * b := by linear_combination h21 / 2
  have hs : S *ᵥ Pi.single 2 1 = ![16 * a, 16 * b, c] := by
    funext k
    rw [mulVec_single_one]
    fin_cases k
    · exact e0
    · exact e1
    · rfl
  -- `c ≡ ±1 (mod 8)`
  have hQs : (csQ A6).evalIn F2 (S *ᵥ Pi.single 2 1) = 16 := by
    rw [evalIn_mulVec_of_mem (csQ A6) σ.2, csQ_A6_eval]; simp [Pi.single_apply]
  rw [hs, csQ_A6_eval] at hQs
  change (16 * a) ^ 2 + (16 * b) ^ 2 + 16 * c ^ 2 = 16 at hQs
  have hc2 : Valued.v ((c - 1) * (c + 1)) ≤ exp (-4 : ℤ) := by
    have e : (c - 1) * (c + 1) = 2 ^ 4 * (-(a ^ 2 + b ^ 2)) := by linear_combination hQs / 16
    rw [e, map_mul, map_pow, h2v, ← WithZero.exp_nsmul]
    have : Valued.v (-(a ^ 2 + b ^ 2)) ≤ 1 := by
      rw [Valuation.map_neg]
      refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ?_)
      · rw [map_pow]; exact pow_le_one' ha 2
      · rw [map_pow]; exact pow_le_one' hb 2
    calc exp (4 • (-1 : ℤ)) * Valued.v (-(a ^ 2 + b ^ 2)) ≤ exp (4 • (-1 : ℤ)) * 1 := mul_le_mul' le_rfl this
      _ = exp (-4 : ℤ) := by rw [mul_one]; norm_num
  have hdisc : ∀ x : ℤᵐ⁰, exp (-2 : ℤ) < x → exp (-1 : ℤ) ≤ x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le hx)
    rw [← exp_log hx0, exp_lt_exp] at hx
    rw [← exp_log hx0, exp_le_exp]
    omega
  have hcancel : ∀ x : ℤᵐ⁰, x * exp (-1 : ℤ) ≤ exp (-4 : ℤ) → x ≤ exp (-3 : ℤ) := by
    intro x hx
    calc x = x * exp (-1 : ℤ) * exp (1 : ℤ) := by rw [mul_assoc, ← exp_add]; norm_num
      _ ≤ exp (-4 : ℤ) * exp (1 : ℤ) := mul_le_mul' hx le_rfl
      _ = exp (-3 : ℤ) := by rw [← exp_add]; norm_num
  have hcases : Valued.v (c - 1) ≤ exp (-3 : ℤ) ∨ Valued.v (c + 1) ≤ exp (-3 : ℤ) := by
    by_cases h : Valued.v (c - 1) ≤ exp (-2 : ℤ)
    · left
      have hp : Valued.v (c + 1) = exp (-1 : ℤ) := by
        rw [show c + 1 = (c - 1) + 2 by ring,
          Valuation.map_add_eq_of_lt_right _ (lt_of_le_of_lt h (by rw [h2v, exp_lt_exp]; norm_num)), h2v]
      refine hcancel _ ?_
      rw [← hp, ← map_mul]; exact hc2
    · right
      have hge := hdisc _ (lt_of_not_ge h)
      refine hcancel _ ?_
      calc Valued.v (c + 1) * exp (-1 : ℤ) ≤ Valued.v (c + 1) * Valued.v (c - 1) := mul_le_mul' le_rfl hge
        _ = Valued.v ((c - 1) * (c + 1)) := by rw [map_mul, mul_comm]
        _ ≤ exp (-4 : ℤ) := hc2
  rcases hcases with h | h
  · exact spinorNorm_mem_H6_key h2 σ ha hb hs h
  · have hQe : (csQ A6).evalIn F2 (Pi.single 2 1) = 16 := by rw [csQ_A6_eval]; simp [Pi.single_apply]
    have hQe0 : (csQ A6).evalIn F2 (Pi.single 2 1) ≠ 0 := by rw [hQe]; norm_num
    set σ₁ := symm (csQ A6) F2 (Pi.single 2 1) * σ
    have hbil : qbil (csQ A6) F2 (Pi.single 2 1) ![16 * a, 16 * b, c] = 32 * c := by
      rw [qbil, hH, single_dotProduct, one_mul, mulVec_diagonal]
      rfl
    have hs1 : mat (csQ A6) F2 σ₁ *ᵥ Pi.single 2 1 = ![16 * a, 16 * b, -c] := by
      rw [mat_mul, ← mulVec_mulVec, hs, symm_mulVec_bil (csQ A6) F2 hQe0, hbil, hQe]
      ext k; fin_cases k <;> simp [Pi.single_apply] <;> ring
    have hk := spinorNorm_mem_H6_key h2 σ₁ ha hb hs1
      (by rw [show -c - 1 = -(c + 1) by ring, Valuation.map_neg]; exact h)
    have hσ : σ = symm (csQ A6) F2 (Pi.single 2 1) * σ₁ := by
      simp only [σ₁, ← mul_assoc, symm_mul_self, one_mul]
    have hmul : spinorNorm (csQ A6) F2 σ =
        spinorNorm (csQ A6) F2 (symm (csQ A6) F2 (Pi.single 2 1)) * spinorNorm (csQ A6) F2 σ₁ := by
      conv_lhs => rw [hσ]
      exact (spinorNormHom (csQ A6) F2 A6_nondeg).map_mul _ _
    rw [hmul, spinorNorm_symm (csQ A6) F2 A6_nondeg hQe0, hQe]
    refine (H6 v).mul_mem ?_ hk
    rw [show (16 : F2) = 4 ^ 2 * 1 by norm_num, sqClassOf_sq_mul (by norm_num) one_ne_zero, sqClassOf_one]
    exact (H6 v).one_mem

end Two

end QuadFormsKB.ConwaySloane
