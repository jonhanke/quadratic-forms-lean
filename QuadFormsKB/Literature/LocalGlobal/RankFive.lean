/-
# Forms of rank $\ge 5$ are isotropic over $\mathbb{Q}_p$: the blueprint

Serre, *A Course in Arithmetic*, IV §2.2, Thm. 6 (Cor. 2). Plan:

* reduce to a **diagonal** form $\langle a_0, \dots, a_{n-1} \rangle$ with $a_i \in \mathbb{Q}^\times$
  (`HM3.exists_isometric_diag`, isotropy invariant under isometry);
* isotropy of any sub-diagonal (a subset of the coordinates) gives isotropy of the whole;
* multiplying a coefficient by a nonzero square does not change isotropy;
* **$p$ odd:** after normalizing, every $a_i$ is $u$ or $p u$ with $u$ a $p$-adic unit; three of
  five share the factor, and a ternary form of units is isotropic
  (`HM3.isotropic_diag_three_iff` + `hilbertSymbol_units`);
* **$p = 2$:** handled separately (Hilbert-symbol counting over $\mathbb{Q}_2$).

Locators are from memory and still `[unverified]`.
-/
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowskiThree

namespace QuadFormsKB.RankFive

open HM3

variable {n : ℕ}

/-- **Isotropy of a sub-form gives isotropy of the form:** if the diagonal form on the first
$m$ coefficients $\langle a_0, \dots, a_{m-1} \rangle$ ($m \le n$) is isotropic over $K$, so is
$\langle a_0, \dots, a_{n-1} \rangle$ (extend the isotropic vector by zeros). -/
@[kb "serre1973" "Ch. IV §1.6 [unverified]"]
theorem isotropicIn_diag_of_prefix (K : Type*) [Field K] [CharZero K] (m : ℕ) (hm : m ≤ n)
    (a : Fin n → ℚ)
    (h : (QuadForm.diag fun i : Fin m => a ⟨i, lt_of_lt_of_le i.2 hm⟩).IsotropicIn K) :
    (QuadForm.diag a).IsotropicIn K := by
  have key : ∀ {k : ℕ} (b : Fin k → ℚ) (x : Fin k → K),
      QuadForm.evalIn K (QuadForm.diag b) x = ∑ i, algebraMap ℚ K (b i) * x i * x i := by
    intro k b x
    unfold QuadForm.evalIn QuadForm.diag
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      split_ifs <;> simp [Matrix.diagonal_apply_ne _ (Ne.symm hj)]
    · simp
  obtain ⟨x, hx0, hx⟩ := h
  set y : Fin n → K := fun j => if hj : (j : ℕ) < m then x ⟨j, hj⟩ else 0 with hy_def
  refine ⟨y, ?_, ?_⟩
  · intro hy
    apply hx0
    funext i
    have := congrFun hy ⟨i, lt_of_lt_of_le i.2 hm⟩
    simpa [hy_def] using this
  · rw [key] at hx ⊢
    refine Eq.trans ?_ hx
    have hs : ∑ j ∈ Finset.univ.map (Fin.castLEEmb hm), algebraMap ℚ K (a j) * y j * y j
        = ∑ j, algebraMap ℚ K (a j) * y j * y j := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      have : ¬ ((j : ℕ) < m) := by
        intro hlt
        apply hj
        simp only [Finset.mem_map, Finset.mem_univ, true_and]
        exact ⟨⟨j, hlt⟩, rfl⟩
      simp [hy_def, this]
    rw [← hs, Finset.sum_map]
    simp [hy_def]
    rfl

/-- **Permuting coefficients does not change isotropy:** for a permutation $\sigma$ of the
coordinates, $\langle a_{\sigma(0)}, \dots \rangle$ is isotropic over $K$ iff
$\langle a_0, \dots \rangle$ is. -/
@[kb "serre1973" "Ch. IV §1.6 [unverified]"]
theorem isotropicIn_diag_perm_iff (K : Type*) [Field K] [CharZero K] (a : Fin n → ℚ)
    (σ : Equiv.Perm (Fin n)) :
    (QuadForm.diag (a ∘ σ)).IsotropicIn K ↔ (QuadForm.diag a).IsotropicIn K := by
  have key : ∀ (b : Fin n → ℚ) (x : Fin n → K),
      QuadForm.evalIn K (QuadForm.diag b) x = ∑ i, algebraMap ℚ K (b i) * x i * x i := by
    intro b x
    unfold QuadForm.evalIn QuadForm.diag
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Matrix.diagonal_apply_ne _ (Ne.symm hj)]
    · simp
  constructor
  · rintro ⟨x, hx, h0⟩
    refine ⟨x ∘ σ.symm, ?_, ?_⟩
    · intro h; apply hx; funext i; simpa using congrFun h (σ i)
    · rw [key] at h0 ⊢
      rw [← h0, ← Equiv.sum_comp σ]
      simp
  · rintro ⟨x, hx, h0⟩
    refine ⟨x ∘ σ, ?_, ?_⟩
    · intro h; apply hx; funext i; simpa using congrFun h (σ.symm i)
    · rw [key] at h0 ⊢
      exact (Equiv.sum_comp σ (fun i => algebraMap ℚ K (a i) * x i * x i)).trans h0

/-- **Scaling one coefficient by a nonzero square does not change isotropy:** if $c \ne 0$, then
$\langle \dots, a_i c^2, \dots \rangle$ is isotropic over $K$ iff $\langle \dots, a_i, \dots \rangle$ is. -/
@[kb "serre1973" "Ch. IV §1.6 [unverified]"]
theorem isotropicIn_diag_mul_sq_iff (K : Type*) [Field K] [CharZero K] (a : Fin n → ℚ) (i : Fin n)
    (c : ℚ) (hc : c ≠ 0) :
    (QuadForm.diag (Function.update a i (a i * c ^ 2))).IsotropicIn K ↔
      (QuadForm.diag a).IsotropicIn K := by
  have key : ∀ (b : Fin n → ℚ) (x : Fin n → K), QuadForm.evalIn K (QuadForm.diag b) x = ∑ j, algebraMap ℚ K (b j) * x j * x j := by
    intro b x
    unfold QuadForm.evalIn QuadForm.diag
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [Matrix.diagonal_apply_ne _ (Ne.symm hk)]
    · simp
  have hcK : algebraMap ℚ K c ≠ 0 := by simpa using hc
  constructor
  · rintro ⟨x, hx, h0⟩
    refine ⟨Function.update x i (algebraMap ℚ K c * x i), ?_, ?_⟩
    · intro h
      apply hx
      funext j
      have := congrFun h j
      by_cases hj : j = i
      · subst hj; simpa [hcK, hc] using this
      · simpa [hj] using this
    · rw [key] at h0 ⊢
      rw [← h0]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      by_cases hj : j = i
      · subst hj; simp; ring
      · simp [hj]
  · rintro ⟨x, hx, h0⟩
    refine ⟨Function.update x i (x i / algebraMap ℚ K c), ?_, ?_⟩
    · intro h
      apply hx
      funext j
      have := congrFun h j
      by_cases hj : j = i
      · subst hj; simpa [hcK, hc] using this
      · simpa [hj] using this
    · rw [key] at h0 ⊢
      rw [← h0]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      by_cases hj : j = i
      · subst hj; simp; field_simp
      · simp [hj]

/-- **Ternary forms of $p$-adic units are isotropic, $p$ odd:** for rationals $a, b, c$ that
are $p$-adic units ($v_p = 0$), $\langle a, b, c \rangle$ is isotropic over $\mathbb{Q}_p$. -/
@[kb "serre1973" "Ch. IV §2.2 [unverified]"]
theorem isotropic_padic_unit_ternary (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (a b c : ℚ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hva : padicValRat p a = 0) (hvb : padicValRat p b = 0) (hvc : padicValRat p c = 0) :
    (QuadForm.diag ![a, b, c]).IsotropicIn ℚ_[p] := by
  have hn : ∀ q : ℚ, q ≠ 0 → padicValRat p q = 0 → ‖((q : ℚ) : ℚ_[p])‖ = 1 := by
    intro q hq hv
    rw [Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero hq, hv]; simp
  have h1 : padicValRat p (-b / a) = 0 := by
    rw [padicValRat.div (neg_ne_zero.mpr hb) ha, padicValRat.neg, hvb, hva]; simp
  have h2 : padicValRat p (-c / a) = 0 := by
    rw [padicValRat.div (neg_ne_zero.mpr hc) ha, padicValRat.neg, hvc, hva]; simp
  have n1 := hn _ (div_ne_zero (neg_ne_zero.mpr hb) ha) h1
  have n2 := hn _ (div_ne_zero (neg_ne_zero.mpr hc) ha) h2
  rw [HM3.isotropic_diag_three_iff ℚ_[p] a b c ha hb hc]
  have := HilbertLocal.hilbertSymbol_units hp2 (PadicInt.mkUnits n1) (PadicInt.mkUnits n2)
  rw [PadicInt.mkUnits_eq, PadicInt.mkUnits_eq] at this
  simpa using this

/-- **Rank $\ge 5$ isotropic over $\mathbb{Q}_p$, $p$ odd, diagonal case.** -/
@[kb "serre1973" "Ch. IV §2.2, Thm. 6 [unverified]"]
theorem isotropic_padic_diag_odd (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (a : Fin n → ℚ)
    (ha : ∀ i, a i ≠ 0) (hn : 5 ≤ n) : (QuadForm.diag a).IsotropicIn ℚ_[p] := by
  have hdiag : ∀ {m : ℕ} (b : Fin m → ℚ) (x : Fin m → ℚ_[p]),
      QuadForm.evalIn ℚ_[p] (QuadForm.diag b) x = ∑ i, algebraMap ℚ ℚ_[p] (b i) * x i ^ 2 := by
    intro m b x
    unfold QuadForm.evalIn QuadForm.diag
    simp only
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp [Matrix.diagonal]; ring
    · intro j _ hj; simp [Matrix.diagonal, Ne.symm hj]
    · simp
  have hilb : ∀ (x y : ℚ_[p]), x ≠ 0 → y ≠ 0 → Even x.valuation → Even y.valuation →
      hilbertSymbol ℚ_[p] x y = 1 := by
    intro x y hx hy hvx hvy
    have H : ∀ z : ℚ_[p], z ≠ 0 → Even z.valuation → ∃ u : ℤ_[p]ˣ, ∃ c : ℚ_[p], c ≠ 0 ∧ z = (u : ℚ_[p]) * c ^ 2 := by
      intro z hz ⟨m, hm⟩
      have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
      have hpR : (0:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
      have hnorm : ‖z * (p : ℚ_[p]) ^ (-(2*m))‖ = 1 := by
        rw [norm_mul, Padic.norm_p_zpow, Padic.norm_eq_zpow_neg_valuation hz, ← zpow_add₀ hpR.ne']
        rw [hm]; ring_nf; simp
      refine ⟨PadicInt.mkUnits hnorm, (p : ℚ_[p]) ^ m, zpow_ne_zero _ hp0, ?_⟩
      simp only [PadicInt.mkUnits]
      show z = z * (p : ℚ_[p]) ^ (-(2*m)) * ((p : ℚ_[p]) ^ m) ^ 2
      rw [mul_assoc, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hp0]
      ring_nf; simp
    obtain ⟨u, c, hc, rfl⟩ := H x hx hvx
    obtain ⟨v, d, hd, rfl⟩ := H y hy hvy
    rw [HM3.hilbertSymbol_mul_sq_left _ _ _ _ hc, hilbertSymbol_comm, HM3.hilbertSymbol_mul_sq_left _ _ _ _ hd]
    exact HilbertLocal.hilbertSymbol_units hp2 v u
  have hvneg1 : (-1 : ℚ_[p]).valuation = 0 := by
    have := Padic.valuation_mul (p := p) (x := -1) (y := -1) (by norm_num) (by norm_num)
    rw [show (-1 : ℚ_[p]) * -1 = 1 by norm_num, Padic.valuation_one] at this
    omega
  have hval : ∀ i j : Fin n, (algebraMap ℚ ℚ_[p] (-a j / a i)).valuation
      = ((a j : ℚ_[p])).valuation - ((a i : ℚ_[p])).valuation := by
    intro i j
    have hi : (a i : ℚ_[p]) ≠ 0 := by exact_mod_cast ha i
    have hj : (a j : ℚ_[p]) ≠ 0 := by exact_mod_cast ha j
    rw [show algebraMap ℚ ℚ_[p] (-a j / a i) = (-1) * ((a j : ℚ_[p]) * (a i : ℚ_[p])⁻¹) by simp; ring]
    rw [Padic.valuation_mul (by norm_num) (mul_ne_zero hj (inv_ne_zero hi)), Padic.valuation_mul hj (inv_ne_zero hi), Padic.valuation_inv, hvneg1]
    ring
  have pig : ∀ f : Fin 5 → Bool, ∃ i j k : Fin 5, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ f i = f j ∧ f i = f k := by decide
  obtain ⟨i', j', k', hij', hik', hjk', hfj, hfk⟩ :=
    pig (fun t => decide (Even ((a (Fin.castLE hn t) : ℚ_[p])).valuation))
  set i := Fin.castLE hn i'
  set j := Fin.castLE hn j'
  set k := Fin.castLE hn k'
  have hij : i ≠ j := fun h => hij' (Fin.castLE_injective hn h)
  have hik : i ≠ k := fun h => hik' (Fin.castLE_injective hn h)
  have hjk : j ≠ k := fun h => hjk' (Fin.castLE_injective hn h)
  simp only [decide_eq_decide] at hfj hfk
  have h3 : (QuadForm.diag ![a i, a j, a k]).IsotropicIn ℚ_[p] := by
    rw [HM3.isotropic_diag_three_iff _ _ _ _ (ha i) (ha j) (ha k)]
    apply hilb
    · exact (map_ne_zero _).mpr (div_ne_zero (neg_ne_zero.mpr (ha j)) (ha i))
    · exact (map_ne_zero _).mpr (div_ne_zero (neg_ne_zero.mpr (ha k)) (ha i))
    · rw [hval, Int.even_sub]; exact hfj.symm
    · rw [hval, Int.even_sub]; exact hfk.symm
  obtain ⟨y, hy0, hy⟩ := h3
  rw [hdiag, Fin.sum_univ_three] at hy
  simp at hy
  refine ⟨fun l => if l = i then y 0 else if l = j then y 1 else if l = k then y 2 else 0, ?_, ?_⟩
  · intro h
    apply hy0
    funext t
    have e0 := congrFun h i
    have e1 := congrFun h j
    have e2 := congrFun h k
    simp [hij, hik, hjk, Ne.symm hij, Ne.symm hik, Ne.symm hjk] at e0 e1 e2
    fin_cases t <;> simp [e0, e1, e2]
  · rw [hdiag]
    have : ∀ l : Fin n, algebraMap ℚ ℚ_[p] (a l) * (if l = i then y 0 else if l = j then y 1 else if l = k then y 2 else 0) ^ 2
        = (if l = i then (a i : ℚ_[p]) * y 0 ^ 2 else 0) + (if l = j then (a j : ℚ_[p]) * y 1 ^ 2 else 0) + (if l = k then (a k : ℚ_[p]) * y 2 ^ 2 else 0) := by
      intro l
      by_cases h1 : l = i
      · subst h1; simp [hij, hik]
      by_cases h2 : l = j
      · subst h2; simp [h1, hjk]
      by_cases h3 : l = k
      · subst h3; simp [h1, h2]
      simp [h1, h2, h3]
    rw [Finset.sum_congr rfl fun l _ => this l]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact hy

/-- **Rank $\ge 5$ isotropic over $\mathbb{Q}_2$, diagonal case** (via Hilbert-symbol counting:
the binary part and the ternary part represent a common square class). -/
@[kb "serre1973" "Ch. IV §2.2, Thm. 6 [unverified]"]
theorem isotropic_two_adic_diag (a : Fin n → ℚ) (ha : ∀ i, a i ≠ 0) (hn : 5 ≤ n) :
    (QuadForm.diag a).IsotropicIn ℚ_[2] := by
  have L1 : ∀ N : ℤ, N % 8 = 1 → ∃ s : ℚ_[2], s ^ 2 = N := by
    intro N hN
    obtain ⟨k, hk⟩ : ∃ k, N = 1 + 8 * k := ⟨N / 8, by omega⟩
    have := @hensels_lemma 2 _ ℤ _ _ (Polynomial.X ^ 2 - Polynomial.C N) 1 (by
      simp [hk, map_ofNat]
      have h8 : ‖(8 : ℤ_[2])‖ = 1/8 := by
        have := @PadicInt.norm_p_pow 2 _ 3
        norm_num at this ⊢; exact this
      have h2 : ‖(2 : ℤ_[2])‖ = 1/2 := by
        have := @PadicInt.norm_p 2 _
        norm_num at this ⊢; exact this
      rw [h8, h2]
      have := PadicInt.norm_le_one (k : ℤ_[2])
      nlinarith [norm_nonneg (k : ℤ_[2])])
    obtain ⟨z, hz, -⟩ := this
    refine ⟨(z : ℚ_[2]), ?_⟩
    simp [sub_eq_zero] at hz
    have := congrArg (fun w : ℤ_[2] => (w : ℚ_[2])) hz
    simpa using this
  have L2 : ∀ o D : ℤ, o % 2 = 1 → D % 8 = 0 → ∃ t : ℚ_[2], t ^ 2 * o = o - D := by
    intro o D ho hD
    have hsq : (o * o) % 8 = 1 := by
      have : o % 8 = 1 ∨ o % 8 = 3 ∨ o % 8 = 5 ∨ o % 8 = 7 := by omega
      rw [Int.mul_emod]; rcases this with h | h | h | h <;> rw [h] <;> norm_num
    obtain ⟨s, hs⟩ := L1 (o * (o - D)) (by
      have : (o * (o - D)) = o * o - o * D := by ring
      rw [this]
      have : (o * D) % 8 = 0 := by rw [Int.mul_emod, hD]; simp
      omega)
    have ho0 : (o : ℚ_[2]) ≠ 0 := by
      have : o ≠ 0 := by omega
      exact_mod_cast this
    refine ⟨s / o, ?_⟩
    rw [div_pow, hs]
    push_cast
    field_simp
  have U_odd : ∀ (x y z s : ℤ), x % 2 = 1 → y % 2 = 1 → z % 2 = 1 → s % 4 = 2 →
      ∃ a b c : ℤ, (a = 1 ∨ b = 1) ∧ (x * a ^ 2 + y * b ^ 2 + z * c ^ 2 + s) % 8 = 0 := by
    intro x y z s hx hy hz hs
    by_cases hxy : x % 4 = y % 4
    · by_cases h8 : (x + y + s) % 8 = 0
      · exact ⟨1, 1, 0, Or.inl rfl, by norm_num; omega⟩
      · exact ⟨1, 1, 2, Or.inl rfl, by norm_num; omega⟩
    · by_cases hxz : x % 4 = z % 4
      · by_cases h8 : (x + z + s) % 8 = 0
        · exact ⟨1, 0, 1, Or.inl rfl, by norm_num; omega⟩
        · exact ⟨1, 2, 1, Or.inl rfl, by norm_num; omega⟩
      · by_cases h8 : (y + z + s) % 8 = 0
        · exact ⟨0, 1, 1, Or.inr rfl, by norm_num; omega⟩
        · exact ⟨2, 1, 1, Or.inr rfl, by norm_num; omega⟩
  have U_even : ∀ (x y z s : ℤ), x % 4 = 2 → y % 4 = 2 → z % 4 = 2 → s % 8 = 4 →
      ∃ a b c : ℤ, (a = 1 ∨ b = 1) ∧ (x * a ^ 2 + y * b ^ 2 + z * c ^ 2 + s) % 16 = 0 := by
    intro x y z s hx hy hz hs
    by_cases hxy : x % 8 = y % 8
    · by_cases h8 : (x + y + s) % 16 = 0
      · exact ⟨1, 1, 0, Or.inl rfl, by norm_num; omega⟩
      · exact ⟨1, 1, 2, Or.inl rfl, by norm_num; omega⟩
    · by_cases hxz : x % 8 = z % 8
      · by_cases h8 : (x + z + s) % 16 = 0
        · exact ⟨1, 0, 1, Or.inl rfl, by norm_num; omega⟩
        · exact ⟨1, 2, 1, Or.inl rfl, by norm_num; omega⟩
      · by_cases h8 : (y + z + s) % 16 = 0
        · exact ⟨0, 1, 1, Or.inr rfl, by norm_num; omega⟩
        · exact ⟨2, 1, 1, Or.inr rfl, by norm_num; omega⟩
  have A_odd : ∀ (x y z u v : ℤ), x % 2 = 1 → y % 2 = 1 → z % 2 = 1 → u % 2 = 1 → v % 2 = 1 →
      ∃ a b c d e : ℤ, (a = 1 ∨ b = 1 ∨ d = 1) ∧
        (x * a ^ 2 + y * b ^ 2 + z * c ^ 2 + u * d ^ 2 + v * e ^ 2) % 8 = 0 := by
    intro x y z u v hx hy hz hu hv
    by_cases huv : u % 4 = v % 4
    · obtain ⟨a, b, c, hab, h⟩ := U_odd x y z (u + v) hx hy hz (by omega)
      refine ⟨a, b, c, 1, 1, by tauto, by norm_num; omega⟩
    · by_cases h8 : (u + v) % 8 = 0
      · exact ⟨0, 0, 0, 1, 1, by tauto, by norm_num; omega⟩
      · exact ⟨2, 0, 0, 1, 1, by tauto, by norm_num; omega⟩
  have A_even : ∀ (x y z u v : ℤ), x % 4 = 2 → y % 4 = 2 → z % 4 = 2 → u % 4 = 2 → v % 4 = 2 →
      ∃ a b c d e : ℤ, (a = 1 ∨ b = 1 ∨ d = 1) ∧
        (x * a ^ 2 + y * b ^ 2 + z * c ^ 2 + u * d ^ 2 + v * e ^ 2) % 16 = 0 := by
    intro x y z u v hx hy hz hu hv
    by_cases huv : u % 8 = v % 8
    · obtain ⟨a, b, c, hab, h⟩ := U_even x y z (u + v) hx hy hz (by omega)
      refine ⟨a, b, c, 1, 1, by tauto, by norm_num; omega⟩
    · by_cases h8 : (u + v) % 16 = 0
      · exact ⟨0, 0, 0, 1, 1, by tauto, by norm_num; omega⟩
      · exact ⟨2, 0, 0, 1, 1, by tauto, by norm_num; omega⟩
  have Core : ∀ (m : Fin 5 → ℤ), (∀ k, m k % 4 ≠ 0) → Monotone (fun k => m k % 2) →
      ∃ w : Fin 5 → ℤ, ∃ j, w j = 1 ∧ ((m j % 2 = 1 ∧ (∑ k, m k * w k ^ 2) % 8 = 0) ∨
        (m j % 2 = 0 ∧ (∑ k, m k * w k ^ 2) % 16 = 0)) := by
    intro m hm mono
    have h01 := mono (show (0 : Fin 5) ≤ 1 by decide)
    have h12 := mono (show (1 : Fin 5) ≤ 2 by decide)
    have h23 := mono (show (2 : Fin 5) ≤ 3 by decide)
    have h34 := mono (show (3 : Fin 5) ≤ 4 by decide)
    simp only at h01 h12 h23 h34
    have e0 := hm 0; have e1 := hm 1; have e2 := hm 2; have e3 := hm 3; have e4 := hm 4
    simp only [Fin.sum_univ_five]
    rcases (by omega : m 0 % 2 = 0 ∨ m 0 % 2 = 1) with p0 | p0 <;>
    rcases (by omega : m 1 % 2 = 0 ∨ m 1 % 2 = 1) with p1 | p1 <;>
    rcases (by omega : m 2 % 2 = 0 ∨ m 2 % 2 = 1) with p2 | p2 <;>
    rcases (by omega : m 3 % 2 = 0 ∨ m 3 % 2 = 1) with p3 | p3 <;>
    rcases (by omega : m 4 % 2 = 0 ∨ m 4 % 2 = 1) with p4 | p4 <;>
    try omega
    · obtain ⟨a, b, c, d, e, h1, h⟩ := A_even (m 0) (m 1) (m 2) (m 3) (m 4) (by omega) (by omega) (by omega) (by omega) (by omega)
      rcases h1 with h1 | h1 | h1
      · exact ⟨![a, b, c, d, e], 0, by simp [h1], Or.inr ⟨p0, by simpa using h⟩⟩
      · exact ⟨![a, b, c, d, e], 1, by simp [h1], Or.inr ⟨p1, by simpa using h⟩⟩
      · exact ⟨![a, b, c, d, e], 3, by simp [h1], Or.inr ⟨p3, by simpa using h⟩⟩
    · obtain ⟨a, b, c, h1, h⟩ := U_even (m 0) (m 1) (m 2) (4 * m 4) (by omega) (by omega) (by omega) (by omega)
      rcases h1 with h1 | h1
      · exact ⟨![a, b, c, 0, 2], 0, by simp [h1], Or.inr ⟨p0, by simp; omega⟩⟩
      · exact ⟨![a, b, c, 0, 2], 1, by simp [h1], Or.inr ⟨p1, by simp; omega⟩⟩
    · obtain ⟨a, b, c, h1, h⟩ := U_even (m 0) (m 1) (m 2) (4 * m 3) (by omega) (by omega) (by omega) (by omega)
      rcases h1 with h1 | h1
      · exact ⟨![a, b, c, 2, 0], 0, by simp [h1], Or.inr ⟨p0, by simp; omega⟩⟩
      · exact ⟨![a, b, c, 2, 0], 1, by simp [h1], Or.inr ⟨p1, by simp; omega⟩⟩
    · obtain ⟨a, b, c, h1, h⟩ := U_odd (m 2) (m 3) (m 4) (m 0) (by omega) (by omega) (by omega) (by omega)
      rcases h1 with h1 | h1
      · exact ⟨![1, 0, a, b, c], 2, by simp [h1], Or.inl ⟨p2, by simp; omega⟩⟩
      · exact ⟨![1, 0, a, b, c], 3, by simp [h1], Or.inl ⟨p3, by simp; omega⟩⟩
    · obtain ⟨a, b, c, h1, h⟩ := U_odd (m 1) (m 2) (m 3) (m 0) (by omega) (by omega) (by omega) (by omega)
      rcases h1 with h1 | h1
      · exact ⟨![1, a, b, c, 0], 1, by simp [h1], Or.inl ⟨p1, by simp; omega⟩⟩
      · exact ⟨![1, a, b, c, 0], 2, by simp [h1], Or.inl ⟨p2, by simp; omega⟩⟩
    · obtain ⟨a, b, c, d, e, h1, h⟩ := A_odd (m 0) (m 1) (m 2) (m 3) (m 4) (by omega) (by omega) (by omega) (by omega) (by omega)
      rcases h1 with h1 | h1 | h1
      · exact ⟨![a, b, c, d, e], 0, by simp [h1], Or.inl ⟨p0, by simpa using h⟩⟩
      · exact ⟨![a, b, c, d, e], 1, by simp [h1], Or.inl ⟨p1, by simpa using h⟩⟩
      · exact ⟨![a, b, c, d, e], 3, by simp [h1], Or.inl ⟨p3, by simpa using h⟩⟩
  have upd : ∀ (g w : Fin 5 → ℚ_[2]) (j : Fin 5) (t : ℚ_[2]),
      ∑ k, g k * (Function.update w j t k) ^ 2 = ∑ k, g k * w k ^ 2 + g j * (t ^ 2 - w j ^ 2) := by
    intro g w j t
    fin_cases j <;> simp [Fin.sum_univ_five, Function.update_apply] <;> ring
  have Mmono : ∀ (m : Fin 5 → ℤ), (∀ k, m k % 4 ≠ 0) → Monotone (fun k => m k % 2) →
      ∃ y : Fin 5 → ℚ_[2], y ≠ 0 ∧ ∑ k, (m k : ℚ_[2]) * y k ^ 2 = 0 := by
    intro m hm mono
    obtain ⟨w, j, hwj, hc⟩ := Core m hm mono
    set S := ∑ k, m k * w k ^ 2 with hSdef
    have hmj := hm j
    obtain ⟨t, ht⟩ : ∃ t : ℚ_[2], t ^ 2 * (m j : ℚ_[2]) = m j - S := by
      rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · obtain ⟨t, ht⟩ := L2 (m j) S h1 (by omega)
        exact ⟨t, ht⟩
      · obtain ⟨t, ht⟩ := L2 (m j / 2) (S / 2) (by omega) (by omega)
        refine ⟨t, ?_⟩
        have e1 : m j = 2 * (m j / 2) := by omega
        have e2 : S = 2 * (S / 2) := by omega
        rw [e1, e2]; push_cast; rw [← sub_eq_zero]
        have : t ^ 2 * ((m j / 2 : ℤ) : ℚ_[2]) - (((m j / 2 : ℤ)) - ((S / 2 : ℤ) : ℚ_[2])) = 0 := by
          rw [ht]; push_cast; ring
        linear_combination 2 * this
    refine ⟨Function.update (fun k => (w k : ℚ_[2])) j t, ?_, ?_⟩
    · intro h0
      have := congrFun h0 j
      simp at this
      rw [this] at ht
      have h3 : ((m j - S : ℤ) : ℚ_[2]) = 0 := by push_cast; rw [← ht]; ring
      have h4 : m j - S = 0 := by exact_mod_cast h3
      rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · rw [upd]
      have hS : ((S : ℤ) : ℚ_[2]) = ∑ k, (m k : ℚ_[2]) * (w k : ℚ_[2]) ^ 2 := by
        rw [hSdef]; push_cast; rfl
      rw [← hS, hwj]
      push_cast
      linear_combination ht
  have hev : ∀ x : Fin n → ℚ_[2], QuadForm.evalIn ℚ_[2] (QuadForm.diag a) x = ∑ i, (a i : ℚ_[2]) * x i ^ 2 := by
    intro x
    unfold QuadForm.evalIn QuadForm.diag
    simp only [Matrix.diagonal_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp; ring
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  have Mall : ∀ m : Fin 5 → ℤ, (∀ k, m k % 4 ≠ 0) →
      ∃ y : Fin 5 → ℚ_[2], y ≠ 0 ∧ ∑ k, (m k : ℚ_[2]) * y k ^ 2 = 0 := by
    intro m hm
    obtain ⟨y, hy0, hy⟩ := Mmono (m ∘ Tuple.sort (fun k => m k % 2)) (fun k => hm _)
      (Tuple.monotone_sort (fun k => m k % 2))
    refine ⟨y ∘ (Tuple.sort (fun k => m k % 2)).symm, ?_, ?_⟩
    · intro h; apply hy0; funext k
      have := congrFun h (Tuple.sort (fun k => m k % 2) k); simpa using this
    · rw [← Equiv.sum_comp (Tuple.sort (fun k => m k % 2))]; simpa using hy
  have := fun k : Fin 5 => exists_squarefree_mul_sq (a (Fin.castLE hn k)) (ha _)
  choose m c hsq hc hmc using this
  have hm4 : ∀ k, m k % 4 ≠ 0 := by
    intro k h
    have h2 : (2:ℤ) * 2 ∣ m k := Int.dvd_of_emod_eq_zero (by simpa using h)
    have := hsq k 2 h2
    rw [Int.isUnit_iff] at this; omega
  obtain ⟨y, hy0, hy⟩ := Mall m hm4
  refine ⟨fun i => if h : i.val < 5 then y ⟨i, h⟩ / c ⟨i, h⟩ else 0, ?_, ?_⟩
  · intro h0
    apply hy0; funext k
    have := congrFun h0 (Fin.castLE hn k)
    have hk : (Fin.castLE hn k).val < 5 := k.2
    simp only [hk, dite_true, Pi.zero_apply] at this
    have hck : (c k : ℚ_[2]) ≠ 0 := by exact_mod_cast hc k
    simp only [Fin.val_castLE, Fin.eta] at this
    simpa [hck] using this
  · rw [hev]
    refine Eq.trans ?_ hy
    symm
    refine Fintype.sum_of_injective (Fin.castLE hn) (Fin.castLE_injective hn) _ _ ?_ ?_
    · intro i hi
      have : ¬ i.val < 5 := by
        intro h5; exact hi ⟨⟨i, h5⟩, rfl⟩
      simp [this]
    · intro k
      have hk : (Fin.castLE hn k).val < 5 := k.2
      simp only [hk, dite_true]
      simp only [Fin.val_castLE, Fin.eta]
      rw [hmc k]
      have hck : (c k : ℚ_[2]) ≠ 0 := by exact_mod_cast hc k
      push_cast
      field_simp

end QuadFormsKB.RankFive
