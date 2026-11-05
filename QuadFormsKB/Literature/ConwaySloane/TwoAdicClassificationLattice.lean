/-
# Conway–Sloane, Ch. 15, Theorem 10: the lattice of a 2-adic block decomposition and O'Meara's 93:29

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §7.3–7.5, pp. 380–381
(`conwaysloane1999`); O. T. O'Meara, *Introduction to Quadratic Forms*, §91C, §93G (`omeara1963`).

Setting: a lattice $M$ on a quadratic space $V$ over $\mathbb Q_2$ with a $\mathbb Z_2$-basis indexed by the variables of a
list $D$ of Cassels blocks whose Gram matrix is the block diagonal matrix of the blocks (`bmat D`). This is the lattice
$\mathbb Z_2^n$ of a form in the shape of Conway–Sloane's Theorem 2 (a Jordan decomposition). The file computes O'Meara's
invariants of $M$ from the 2-adic symbol $\sigma$ = `blockSymbol D`:
* the sublattices spanned by the blocks of exponent $k$ form a Jordan splitting of $M$ (`isJordanSplitting_comp`), with
  scale $2^k$, norm $2^{k + \delta}$ ($\delta = 0$ for type I, $1$ for type II) and rank $n_{2^k}$;
* the Jordan chain $M_{(i)}$ is spanned by the blocks of exponent $\le k_i$ (`jordanChain_comp`).
-/
import QuadFormsKB.Literature.ConwaySloane.TwoAdicClassificationBlocks
import QuadFormsKB.Literature.OMeara.Sec93G29Main
import QuadFormsKB.Literature.OMeara.Sec94
import QuadFormsKB.Literature.Cassels.Ch8.LatticeBridge
import QuadFormsKB.Literature.Cassels.Ch14.LocalClassesTwo

noncomputable section

namespace QuadFormsKB.ConwaySloane.TwoAdic

open OMeara Submodule Module Matrix Finset
open Cassels (DyBlock)
open scoped Pointwise

/-- $\mathbb Z_p$ is a Henselian local ring (it is complete for its maximal ideal; Mathlib's
`IsAdicComplete.henselianRing`). -/
instance henselianLocalRing_padicInt (p : ℕ) [Fact p.Prime] : HenselianLocalRing ℤ_[p] where
  is_henselian f hf a₀ h₁ h₂ :=
    HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal ℤ_[p]) f hf a₀ h₁
      (h₂.map (Ideal.Quotient.mk _))

/-! ### Powers of 2 and their spans -/

theorem norm_two_pow (a : ℕ) : ‖(2 : ℚ_[2]) ^ a‖ = (2 : ℝ) ^ (-(a : ℤ)) := by
  rw [norm_pow, show ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ by simpa using Padic.norm_p (p := 2)]
  rw [_root_.zpow_neg, zpow_natCast, inv_pow]

/-- `ℤ₂ ∙ 2^a ≤ ℤ₂ ∙ 2^b` iff `b ≤ a`. -/
theorem span_two_pow_le_iff (a b : ℕ) :
    (ℤ_[2] ∙ (2 : ℚ_[2]) ^ a) ≤ (ℤ_[2] ∙ (2 : ℚ_[2]) ^ b) ↔ b ≤ a := by
  rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    have h1 : ‖(2 : ℚ_[2]) ^ a‖ ≤ ‖(2 : ℚ_[2]) ^ b‖ := by
      rw [← hc, Algebra.smul_def, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one c)
    rw [norm_two_pow, norm_two_pow] at h1
    have := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 h1
    omega
  · intro h
    refine ⟨((2 : ℕ) : ℤ_[2]) ^ (a - b), ?_⟩
    rw [Algebra.smul_def, PadicInt.algebraMap_apply, PadicInt.coe_pow, PadicInt.coe_natCast, Nat.cast_ofNat,
      ← pow_add, Nat.sub_add_cancel h]

theorem span_two_pow_lt {a b : ℕ} (h : a < b) :
    (ℤ_[2] ∙ (2 : ℚ_[2]) ^ b) < (ℤ_[2] ∙ (2 : ℚ_[2]) ^ a) := by
  refine lt_of_le_of_ne ((span_two_pow_le_iff b a).2 h.le) fun he => ?_
  have := (span_two_pow_le_iff a b).1 he.ge
  omega

theorem span_two_pow_inj {a b : ℕ} (h : (ℤ_[2] ∙ (2 : ℚ_[2]) ^ a) = (ℤ_[2] ∙ (2 : ℚ_[2]) ^ b)) : a = b :=
  le_antisymm ((span_two_pow_le_iff b a).1 h.ge) ((span_two_pow_le_iff a b).1 h.le)

theorem mem_span_two_pow (a : ℕ) (z : ℤ_[2]) : (2 : ℚ_[2]) ^ a * (z : ℚ_[2]) ∈ ℤ_[2] ∙ (2 : ℚ_[2]) ^ a :=
  Submodule.mem_span_singleton.2 ⟨z, by rw [Algebra.smul_def, PadicInt.algebraMap_apply, mul_comm]⟩

/-! ### Square classes of 2-adic units -/


theorem intCast_mem_span_two_pow_iff (z : ℤ) (m : ℕ) :
    (z : ℚ_[2]) ∈ (ℤ_[2] ∙ (2 : ℚ_[2]) ^ m) ↔ (2 : ℤ) ^ m ∣ z := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h
    have h1 : ‖(z : ℚ_[2])‖ ≤ ((2 : ℕ) : ℝ) ^ (-(m : ℤ)) := by
      rw [← hc, Algebra.smul_def, norm_mul, norm_two_pow]
      push_cast
      exact mul_le_of_le_one_left (by positivity) (PadicInt.norm_le_one c)
    have := (Padic.norm_int_le_pow_iff_dvd (p := 2) z m).1 h1
    exact_mod_cast this
  · rintro ⟨w, rfl⟩
    exact Submodule.mem_span_singleton.2 ⟨(w : ℤ_[2]), by
      rw [Algebra.smul_def, PadicInt.algebraMap_apply]; push_cast; ring⟩

theorem unit_sq_eq {ε : ℤ_[2]} (hε : IsUnit ε) : ∃ y : ℤ_[2], ε ^ 2 = 1 + 8 * y := by
  obtain ⟨u0, hu0, c, hc⟩ := Cassels.dyadic_exists_mod8 hε
  have hε' : ε = u0 + 8 * c := by rw [← sub_eq_iff_eq_add']; rw [hc]; norm_num
  rcases hu0 with rfl | rfl | rfl | rfl
  · exact ⟨2 * c + 8 * c ^ 2, by rw [hε']; push_cast; ring⟩
  · exact ⟨1 + 6 * c + 8 * c ^ 2, by rw [hε']; push_cast; ring⟩
  · exact ⟨3 + 10 * c + 8 * c ^ 2, by rw [hε']; push_cast; ring⟩
  · exact ⟨6 + 14 * c + 8 * c ^ 2, by rw [hε']; push_cast; ring⟩

theorem mem_span_mul_unit {x : ℚ_[2]} {v : ℤ_[2]} (hv : IsUnit v) (m : ℕ) :
    x * (v : ℚ_[2]) ∈ (ℤ_[2] ∙ (2 : ℚ_[2]) ^ m) ↔ x ∈ (ℤ_[2] ∙ (2 : ℚ_[2]) ^ m) := by
  constructor
  · intro h
    have := Submodule.smul_mem _ (↑hv.unit⁻¹ : ℤ_[2]) h
    rwa [Algebra.smul_def, PadicInt.algebraMap_apply, mul_left_comm, ← PadicInt.coe_mul, hv.val_inv_mul,
      PadicInt.coe_one, mul_one] at this
  · intro h
    have := Submodule.smul_mem _ v h
    rwa [Algebra.smul_def, PadicInt.algebraMap_apply, mul_comm] at this

theorem span_two_pow_mono {a b : ℕ} (h : b ≤ a) : (ℤ_[2] ∙ (2 : ℚ_[2]) ^ a) ≤ (ℤ_[2] ∙ (2 : ℚ_[2]) ^ b) :=
  (span_two_pow_le_iff a b).2 h

/-- **$U/U' \cong 1 \bmod 2^m$** (O'Meara's `SqEquivMod`, §93A) for odd integers: $2^{\min(m,3)} \mid U - U'$. -/
theorem sqEquivMod_iff {m : ℕ} (hm : 1 ≤ m) {U U' : ℤ} (hU : Odd U) (hU' : Odd U') :
    SqEquivMod (ℤ_[2] ∙ (2 : ℚ_[2]) ^ m) ((U : ℚ_[2]) / U') 1 ↔ (2 : ℤ) ^ (min m 3) ∣ U - U' := by
  have hUu : IsUnit (U : ℤ_[2]) := Cassels.dyadic_isUnit_int_cast_of_odd hU
  have hU'u : IsUnit (U' : ℤ_[2]) := Cassels.dyadic_isUnit_int_cast_of_odd hU'
  have hU'0 : (U' : ℚ_[2]) ≠ 0 := by
    have : (U' : ℤ) ≠ 0 := fun h => by rw [h] at hU'; exact absurd hU' (by decide)
    exact_mod_cast this
  have hsplit : ∀ y : ℚ_[2], (U : ℚ_[2]) / U' - y = ((U : ℚ_[2]) - U' * y) * ((↑hU'u.unit⁻¹ : ℤ_[2]) : ℚ_[2]) := by
    intro y
    have h1 : ((↑hU'u.unit⁻¹ : ℤ_[2]) : ℚ_[2]) = (U' : ℚ_[2])⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← PadicInt.coe_intCast, ← PadicInt.coe_mul, hU'u.val_inv_mul, PadicInt.coe_one]
    rw [h1]; field_simp
  have hinvu : IsUnit (↑hU'u.unit⁻¹ : ℤ_[2]) := Units.isUnit _
  constructor
  · rintro ⟨-, ε, hε, hmem⟩
    obtain ⟨y, hy⟩ := unit_sq_eq hε
    rw [one_mul, ← map_pow, hy, hsplit, mem_span_mul_unit hinvu, PadicInt.algebraMap_apply] at hmem
    have h3 : (8 : ℚ_[2]) * (U' : ℚ_[2]) * (y : ℚ_[2]) ∈ (ℤ_[2] ∙ (2 : ℚ_[2]) ^ (min m 3)) := by
      refine span_two_pow_mono (min_le_right m 3) ?_
      rw [show (8 : ℚ_[2]) * U' * y = (2 : ℚ_[2]) ^ 3 * (((U' : ℤ_[2]) * y : ℤ_[2]) : ℚ_[2]) by
        push_cast; ring]
      exact mem_span_two_pow _ _
    have h4 := Submodule.add_mem _ (span_two_pow_mono (min_le_left m 3) hmem) h3
    rw [← intCast_mem_span_two_pow_iff]
    have e : (U : ℚ_[2]) - U' * ((1 + 8 * y : ℤ_[2]) : ℚ_[2]) + 8 * U' * y = ((U - U' : ℤ) : ℚ_[2]) := by
      rw [PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_one]
      show (U : ℚ_[2]) - U' * (1 + 8 * (y : ℚ_[2])) + 8 * U' * y = ((U - U' : ℤ) : ℚ_[2])
      push_cast; ring
    rwa [e] at h4
  · intro h
    refine ⟨⟨(U : ℤ_[2]) * ↑hU'u.unit⁻¹, hUu.mul hinvu, ?_⟩, ?_⟩
    · rw [map_mul, PadicInt.algebraMap_apply, PadicInt.algebraMap_apply, mul_one]
      have := hsplit 0
      simpa using this
    rcases Nat.lt_or_ge m 3 with hm3 | hm3
    · refine ⟨1, isUnit_one, ?_⟩
      rw [map_one, one_pow, mul_one, show (1 : ℚ_[2]) = 1 * 1 by ring, ← one_mul (1 : ℚ_[2]), hsplit,
        mem_span_mul_unit hinvu]
      rw [min_eq_left hm3.le] at h
      have := (intCast_mem_span_two_pow_iff (U - U') m).2 h
      push_cast at this
      simpa using this
    · rw [min_eq_right hm3] at h
      obtain ⟨w, hw⟩ := h
      obtain ⟨z, hz, hzu⟩ := Composition.exists_sq_one_add_eight (w * ↑hU'u.unit⁻¹)
      refine ⟨z, hzu, ?_⟩
      have hz' : (z : ℚ_[2]) ^ 2 = 1 + 8 * ((w : ℚ_[2]) * ((↑hU'u.unit⁻¹ : ℤ_[2]) : ℚ_[2])) := by
        have := congrArg (fun t : ℤ_[2] => (t : ℚ_[2])) hz
        simp only [PadicInt.coe_pow, PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_one,
          PadicInt.coe_intCast] at this
        exact this
      have hzz : (U : ℚ_[2]) / U' - 1 * (algebraMap ℤ_[2] ℚ_[2] z) ^ 2 = 0 := by
        have h1 : ((↑hU'u.unit⁻¹ : ℤ_[2]) : ℚ_[2]) * U' = 1 := by
          rw [← PadicInt.coe_intCast, ← PadicInt.coe_mul, hU'u.val_inv_mul, PadicInt.coe_one]
        have hUw : (U : ℚ_[2]) = U' + 8 * w := by
          have := congrArg (fun z : ℤ => (z : ℚ_[2])) hw
          push_cast at this; linear_combination this
        rw [one_mul, PadicInt.algebraMap_apply, hz', hsplit, hUw]
        linear_combination (-8 * (w : ℚ_[2]) * ((↑hU'u.unit⁻¹ : ℤ_[2]) : ℚ_[2])) * h1
      rw [hzz]; exact zero_mem _

/-- The conditions of `OMPair` (i) for odd integers: $2^{\min(m,3)} \mid U - U'$. -/
theorem two_pow_min_dvd_iff {m : ℕ} (hm : 1 ≤ m) {U U' : ℤ} (hU : Odd U) (hU' : Odd U') :
    (2 : ℤ) ^ (min m 3) ∣ U - U' ↔
      (2 ≤ m → 2 * ((U : ZMod 8) - U') = 0) ∧ (3 ≤ m → (U : ZMod 8) = U') := by
  have e1 : 2 * ((U : ZMod 8) - U') = 0 ↔ (8 : ℤ) ∣ 2 * (U - U') := by
    have := ZMod.intCast_zmod_eq_zero_iff_dvd (2 * (U - U')) 8
    push_cast at this; exact this
  have e2 : (U : ZMod 8) = U' ↔ (8 : ℤ) ∣ U - U' := by
    have := ZMod.intCast_zmod_eq_zero_iff_dvd (U - U') 8
    push_cast at this; rw [← this, sub_eq_zero]
  rw [e1, e2]
  obtain ⟨a, rfl⟩ := hU
  obtain ⟨b, rfl⟩ := hU'
  rcases Nat.lt_or_ge m 2 with h | h
  · have : m = 1 := by omega
    subst this
    simp only [show min 1 3 = 1 from rfl, pow_one]
    constructor
    · intro _; exact ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
    · intro _; exact ⟨a - b, by ring⟩
  rcases Nat.lt_or_ge m 3 with h' | h'
  · have : m = 2 := by omega
    subst this
    simp only [show min 2 3 = 2 from rfl]
    constructor
    · rintro ⟨c, hc⟩; exact ⟨fun _ => ⟨c, by omega⟩, fun h => absurd h (by omega)⟩
    · rintro ⟨h1, -⟩; obtain ⟨c, hc⟩ := h1 le_rfl; exact ⟨c, by omega⟩
  · rw [min_eq_right h']
    constructor
    · rintro ⟨c, hc⟩; exact ⟨fun _ => ⟨2 * c, by omega⟩, fun _ => ⟨c, by omega⟩⟩
    · rintro ⟨-, h2⟩; obtain ⟨c, hc⟩ := h2 h'; exact ⟨c, by omega⟩

/-- The oddity of $\langle 2^NW\rangle$, $W$ odd, is `oddE N W`. -/
theorem oddityEntry_eq_oddE (N : ℕ) {W : ℤ} (hW : Odd W) :
    oddityEntry (2 ^ N * W) = oddE (N : ZMod 8) (W : ZMod 8) := by
  rw [Rational.oddityEntry_two_pow_mul N W (by rintro ⟨c, rfl⟩; obtain ⟨d, hd⟩ := hW; omega)]
  unfold oddE
  rw [four_mul_natCast_mod_two]
  congr 1
  have ho : Odd N ↔ N % 2 = 1 := Nat.odd_iff
  by_cases hP : ((W : ZMod 8) = 3 ∨ (W : ZMod 8) = 5) <;>
    rcases Nat.mod_two_eq_zero_or_one N with h | h <;> simp [ho, h, hP]

/-! ### Representations of quadratic spaces by orthogonal bases -/

section Rep

variable {U₁ U₂ : Type*} [AddCommGroup U₁] [Module ℚ_[2] U₁] [AddCommGroup U₂] [Module ℚ_[2] U₂]

theorem rep_of_isometryEquiv {Q₁ : QuadraticForm ℚ_[2] U₁} {Q₂ : QuadraticForm ℚ_[2] U₂} (e : Q₁.IsometryEquiv Q₂)
    {n : ℕ} {M : Matrix (Fin n) (Fin n) ℚ_[2]} (h : D18.Rep Q₁ M) : D18.Rep Q₂ M := by
  obtain ⟨b, hb⟩ := h
  refine ⟨b.map e.toLinearEquiv, ?_⟩
  rw [← hb]
  ext i j
  simp only [OMeara.gram, of_apply, Basis.map_apply]
  exact Resplit.bil_isometry e (b i) (b j)

theorem isometryEquiv_of_rep {Q₁ : QuadraticForm ℚ_[2] U₁} {Q₂ : QuadraticForm ℚ_[2] U₂} {n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℚ_[2]} (h₁ : D18.Rep Q₁ M) (h₂ : D18.Rep Q₂ M) : Nonempty (Q₁.IsometryEquiv Q₂) := by
  obtain ⟨b₁, hb₁⟩ := h₁
  obtain ⟨b₂, hb₂⟩ := h₂
  let φ : U₁ ≃ₗ[ℚ_[2]] U₂ := b₁.equiv b₂ (Equiv.refl _)
  refine ⟨{ φ with map_app' := fun x => ?_ }⟩
  have hx : x = ∑ i, b₁.repr x i • b₁ i := (b₁.sum_repr x).symm
  have hφx : φ x = ∑ i, b₁.repr x i • b₂ i := by
    have := congrArg φ hx
    rw [map_sum] at this
    simpa only [LinearEquiv.map_smul, φ, Basis.equiv_apply, Equiv.refl_apply] using this
  show Q₂ (φ x) = Q₁ x
  rw [hφx, D18.Q_sum_gram, hb₂]
  conv_rhs => rw [hx, D18.Q_sum_gram, hb₁]

theorem rep_prod_sq {Q₁ : QuadraticForm ℚ_[2] U₁} {n : ℕ} {w : Fin n → ℚ_[2]} (h : D18.Rep Q₁ (diagonal w))
    (a : ℚ_[2]) : D18.Rep (Q₁.prod (a • (QuadraticMap.sq : QuadraticForm ℚ_[2] ℚ_[2])))
      (diagonal (Fin.snoc w a : Fin (n + 1) → ℚ_[2])) := by
  obtain ⟨e, he⟩ := h
  refine ⟨(e.prod (Basis.singleton (Fin 1) ℚ_[2])).reindex finSumFinEquiv, ?_⟩
  have hbe : ∀ i j, bil Q₁ (e i) (e j) = diagonal w i j := fun i j => by rw [← he]; rfl
  have h0 : ∀ x, bil Q₁ 0 x = 0 := fun x => by simp [OMeara.bil]
  have h0' : ∀ x, bil Q₁ x 0 = 0 := fun x => by simp [OMeara.bil]
  ext i j
  simp only [OMeara.gram, of_apply, Basis.reindex_apply, Resplit.bil_prod, Resplit.bil_smul_sq]
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [finSumFinEquiv_symm_last, diagonal_apply, h0, h0']
  · simp [finSumFinEquiv_symm_last, finSumFinEquiv_symm_apply_castSucc, diagonal_apply,
      (Fin.castSucc_lt_last j).ne', h0, h0']
  · simp [finSumFinEquiv_symm_last, finSumFinEquiv_symm_apply_castSucc, diagonal_apply,
      (Fin.castSucc_lt_last i).ne, h0, h0']
  · simp only [finSumFinEquiv_symm_apply_castSucc, Basis.prod_apply_inl_fst, Basis.prod_apply_inl_snd, hbe,
      mul_zero, add_zero, diagonal_apply, Fin.castSucc_inj, Fin.snoc_castSucc]

end Rep

/-! ### $FA \to FB \perp \langle c\rangle$ by Hasse invariants -/

section SpanRep

variable {V : Type*} [AddCommGroup V] [Module ℚ_[2] V] [Module ℤ_[2] V] [IsScalarTower ℤ_[2] ℚ_[2] V]
variable (Q : QuadraticForm ℚ_[2] V)

theorem prod_snoc {m : ℕ} (w : Fin m → ℚ_[2]) (a : ℚ_[2]) :
    ∏ i, (Fin.snoc w a : Fin (m + 1) → ℚ_[2]) i = (∏ i, w i) * a := by
  rw [Fin.prod_univ_castSucc]; simp [Fin.snoc_castSucc, Fin.snoc_last]

theorem snoc_ne_zero {m : ℕ} {w : Fin m → ℚ_[2]} (hw : ∀ i, w i ≠ 0) {a : ℚ_[2]} (ha : a ≠ 0) :
    ∀ i, (Fin.snoc w a : Fin (m + 1) → ℚ_[2]) i ≠ 0 := by
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simpa [Fin.snoc_last] using ha
  · simpa [Fin.snoc_castSucc] using hw i

/-- **$FA \to FB \perp \langle c\rangle$ by Hasse invariants** (O'Meara 1963, §63B, 63:21, for orthogonal bases): if
$FA \cong \langle w_A\rangle$ and $FB \cong \langle w_B\rangle$ (orthogonal bases), then $FA$ is represented by
$FB \perp \langle c\rangle$ iff $\langle w_B, c\rangle$ and $\langle w_A, c\prod w_B\prod w_A\rangle$ (which have the same
discriminant) have the same Hasse invariant. -/
theorem spanRepresents_iff_hasse {A B : Submodule ℤ_[2] V} (hAreg : IsRegular Q A) {m : ℕ}
    {wA wB : Fin m → ℚ_[2]} (hwA : ∀ i, wA i ≠ 0) (hwB : ∀ i, wB i ≠ 0)
    (hA : D18.Rep (D18.subQ Q A) (diagonal wA)) (hB : D18.Rep (D18.subQ Q B) (diagonal wB))
    {c : ℚ_[2]} (hc : c ≠ 0) :
    SpanRepresents Q A B c ↔ PadicClass.hasseVec (Fin.snoc wB c : Fin (m + 1) → ℚ_[2]) =
      PadicClass.hasseVec (Fin.snoc wA (c * (∏ i, wB i) * ∏ i, wA i) : Fin (m + 1) → ℚ_[2]) := by
  have hPA : (∏ i, wA i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hwA i
  have hPB : (∏ i, wB i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hwB i
  set a₀ := c * (∏ i, wB i) * ∏ i, wA i with ha₀
  have ha₀0 : a₀ ≠ 0 := mul_ne_zero (mul_ne_zero hc hPB) hPA
  have hX₀ := rep_prod_sq hA a₀
  have hY := rep_prod_sq hB c
  have key : RepTransfer.Rep (D18.subQ Q A)
      ((D18.subQ Q B).prod (c • (QuadraticMap.sq : QuadraticForm ℚ_[2] ℚ_[2]))) ↔
      D18.Rep ((D18.subQ Q B).prod (c • (QuadraticMap.sq : QuadraticForm ℚ_[2] ℚ_[2])))
        (diagonal (Fin.snoc wA a₀ : Fin (m + 1) → ℚ_[2])) := by
    constructor
    · intro hR
      obtain ⟨eA, heA⟩ := hA
      obtain ⟨eB, heB⟩ := hB
      haveI : FiniteDimensional ℚ_[2] (D18.spanF ℚ_[2] A) := Module.Finite.of_basis eA
      haveI : FiniteDimensional ℚ_[2] (D18.spanF ℚ_[2] B) := Module.Finite.of_basis eB
      have h₁ := RepTransfer.nondegenerate_subQ Q hAreg
      have hd' : (OMeara.gram (D18.subQ Q B) fun i => eB i).det ≠ 0 := by
        rw [heB, det_diagonal]; exact hPB
      obtain ⟨a₁, s, hs, ha₁, hdisc, ⟨ψ⟩⟩ := Resplit.rep_complement_disc h₁ hc eA eB hd' hR
      rw [heA, heB, det_diagonal, det_diagonal] at hdisc
      have hX₁ := rep_prod_sq ⟨eA, heA⟩ a₁
      set r := s / ∏ i, wA i
      have hr : r ≠ 0 := div_ne_zero hs hPA
      have hPm : IsUnit (diagonal (Fin.snoc (fun _ => (1 : ℚ_[2])) r⁻¹ : Fin (m + 1) → ℚ_[2])).det := by
        rw [det_diagonal, isUnit_iff_ne_zero]
        exact Finset.prod_ne_zero_iff.2 fun i _ => snoc_ne_zero (fun _ => one_ne_zero) (inv_ne_zero hr) i
      have hX₁' := D18.rep_congr _ hX₁ hPm
      have hmat : diagonal (Fin.snoc (fun _ => (1 : ℚ_[2])) r⁻¹ : Fin (m + 1) → ℚ_[2]) *
          diagonal (Fin.snoc wA a₁ : Fin (m + 1) → ℚ_[2]) *
          (diagonal (Fin.snoc (fun _ => (1 : ℚ_[2])) r⁻¹ : Fin (m + 1) → ℚ_[2]))ᵀ =
          diagonal (Fin.snoc wA a₀ : Fin (m + 1) → ℚ_[2]) := by
        rw [diagonal_transpose, diagonal_mul_diagonal, diagonal_mul_diagonal]
        congr 1
        funext i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · simp only [Fin.snoc_last, r, ha₀]
          field_simp
          linear_combination hdisc
        · simp [Fin.snoc_castSucc]
      rw [hmat] at hX₁'
      exact rep_of_isometryEquiv ψ hX₁'
    · intro hR
      obtain ⟨φ⟩ := isometryEquiv_of_rep hX₀ hR
      refine ⟨φ.toLinearEquiv.toLinearMap ∘ₗ LinearMap.inl ℚ_[2] _ _, ?_, fun x => ?_⟩
      · exact φ.toLinearEquiv.injective.comp LinearMap.inl_injective
      · show ((D18.subQ Q B).prod (c • (QuadraticMap.sq : QuadraticForm ℚ_[2] ℚ_[2]))) (φ (x, 0)) =
          D18.subQ Q A x
        rw [φ.map_app]
        simp [QuadraticMap.prod_apply]
  rw [RepTransfer.spanRepresents_iff_rep, key,
    D18.rep_diag_iff _ (PadicClass.localHilbertField_padic 2) (snoc_ne_zero hwB hc) (snoc_ne_zero hwA ha₀0) hY]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨∏ i, wA i, hPA, ?_⟩, h⟩
    rw [prod_snoc, prod_snoc, ha₀]; ring

end SpanRep

/-! ### Hasse invariants of integer vectors and oddities -/

theorem cast_snoc {m : ℕ} (v : Fin m → ℤ) (x : ℤ) :
    (fun i => (((Fin.snoc v x : Fin (m + 1) → ℤ) i : ℤ) : ℚ_[2])) =
      (Fin.snoc (fun i => (v i : ℚ_[2])) (x : ℚ_[2]) : Fin (m + 1) → ℚ_[2]) := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i <;> simp [Fin.snoc_last, Fin.snoc_castSucc]

theorem hasseVec_intCast {n : ℕ} (a : Fin n → ℤ) :
    PadicClass.hasseVec (fun i => (a i : ℚ_[2])) =
      (RatPlace.finite ⟨2, Nat.prime_two⟩).hasseSerre (fun i => (a i : ℚ)) := by
  rw [show (RatPlace.finite ⟨2, Nat.prime_two⟩).hasseSerre (fun i => (a i : ℚ)) =
    hasseInvariant ℚ_[2] (fun i => (a i : ℚ)) from RatPlace.hasseSerre_finite ⟨2, Nat.prime_two⟩ _]
  simp only [hasseInvariant, PadicClass.hasseVec, map_intCast]

theorem oddity_snoc {m : ℕ} (v : Fin m → ℤ) (x : ℤ) :
    oddity (Fin.snoc v x : Fin (m + 1) → ℤ) = oddity v + oddityEntry x := by
  unfold oddity
  rw [Fin.sum_univ_castSucc]; simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- **The Hasse condition of `spanRepresents_iff_hasse` for integer weights, as an oddity equation.** -/
theorem hasse_snoc_iff {m : ℕ} {vA vB : Fin m → ℤ} (hA : ∀ i, vA i ≠ 0) (hB : ∀ i, vB i ≠ 0) (u : ℕ) :
    PadicClass.hasseVec (Fin.snoc (fun i => (vB i : ℚ_[2])) ((2 : ℚ_[2]) ^ u) : Fin (m + 1) → ℚ_[2]) =
      PadicClass.hasseVec (Fin.snoc (fun i => (vA i : ℚ_[2]))
        ((2 : ℚ_[2]) ^ u * (∏ i, (vB i : ℚ_[2])) * ∏ i, (vA i : ℚ_[2])) : Fin (m + 1) → ℚ_[2]) ↔
      oddity vA + oddityEntry (2 ^ u * (∏ i, vB i) * ∏ i, vA i) = oddity vB + 1 := by
  have hPA : (∏ i, vA i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hA i
  have hPB : (∏ i, vB i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hB i
  have h2u : (2 : ℤ) ^ u ≠ 0 := pow_ne_zero _ two_ne_zero
  set a : Fin (m + 1) → ℤ := Fin.snoc vA (2 ^ u * (∏ i, vB i) * ∏ i, vA i)
  set b : Fin (m + 1) → ℤ := Fin.snoc vB (2 ^ u)
  have ha : ∀ i, a i ≠ 0 := by
    intro i; refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [a, Fin.snoc_last]; exact mul_ne_zero (mul_ne_zero h2u hPB) hPA
    · simpa [a, Fin.snoc_castSucc] using hA i
  have hb : ∀ i, b i ≠ 0 := by
    intro i; refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [b, Fin.snoc_last]; exact h2u
    · simpa [b, Fin.snoc_castSucc] using hB i
  have e1 : (Fin.snoc (fun i => (vB i : ℚ_[2])) ((2 : ℚ_[2]) ^ u) : Fin (m + 1) → ℚ_[2]) =
      fun i => ((b i : ℤ) : ℚ_[2]) := by rw [cast_snoc]; push_cast; rfl
  have e2 : (Fin.snoc (fun i => (vA i : ℚ_[2])) ((2 : ℚ_[2]) ^ u * (∏ i, (vB i : ℚ_[2])) * ∏ i, (vA i : ℚ_[2])) :
      Fin (m + 1) → ℚ_[2]) = fun i => ((a i : ℤ) : ℚ_[2]) := by rw [cast_snoc]; push_cast; rfl
  rw [e1, e2, hasseVec_intCast, hasseVec_intCast]
  have hoa := oddity_eq_hasse a ha
  have hob := oddity_eq_hasse b hb
  have hprod : (∏ i, a i) = (∏ i, b i) * (∏ i, vA i) ^ 2 := by
    simp only [a, b, Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]; ring
  have hent : oddityEntry (∏ i, a i) = oddityEntry (∏ i, b i) := by
    rw [hprod]; exact Rational.oddityEntry_mul_sq (Finset.prod_ne_zero_iff.2 fun i _ => hb i) hPA
  rw [eq_comm, ← Rational.sgn4_inj (hasseSerre_pm _ _) (hasseSerre_pm _ _)]
  have hoa' : oddity a = oddity vA + oddityEntry (2 ^ u * (∏ i, vB i) * ∏ i, vA i) := oddity_snoc _ _
  have hob' : oddity b = oddity vB + 1 := by
    rw [oddity_snoc, show (2 : ℤ) ^ u = 2 ^ u * 1 by ring, oddityEntry_two_pow]
  constructor
  · intro h; rw [← hoa', ← hob', hoa, hob, hent, h]
  · intro h
    rw [← hoa', ← hob', hoa, hob, hent] at h
    exact add_left_cancel h

/-! ### Sublattices spanned by blocks -/

/-- The variables of the blocks $j$ satisfying `P`. -/
abbrev SIdx (D : List DyBlock) (P : Fin D.length → Prop) : Type := Σ j : {j // P j}, Fin (D.get j.1).dim

section Lattice

variable {V : Type*} [AddCommGroup V] [Module ℚ_[2] V] [Module ℤ_[2] V] [IsScalarTower ℤ_[2] ℚ_[2] V]
variable (Q : QuadraticForm ℚ_[2] V)
variable {D : List DyBlock} {M : Submodule ℤ_[2] V} (bM : Basis (BIdx D) ℤ_[2] M)

/-- The basis vectors of the blocks satisfying `P`. -/
def selVec (P : Fin D.length → Prop) (y : SIdx D P) : V := (bM ⟨y.1.1, y.2⟩ : V)

theorem selVec_linIndep (P : Fin D.length → Prop) : LinearIndependent ℤ_[2] (selVec bM P) := by
  have h1 : LinearIndependent ℤ_[2] (fun x => (bM x : V)) :=
    bM.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hinj : Function.Injective (fun y : SIdx D P => (⟨y.1.1, y.2⟩ : BIdx D)) := by
    rintro ⟨⟨j, hj⟩, r⟩ ⟨⟨j', hj'⟩, r'⟩ h
    simp only [Sigma.mk.inj_iff] at h
    obtain ⟨rfl, h2⟩ := h
    cases h2
    rfl
  exact h1.comp _ hinj

/-- The sublattice spanned by the blocks satisfying `P`. -/
def selLat (P : Fin D.length → Prop) : Submodule ℤ_[2] V := span ℤ_[2] (Set.range (selVec bM P))

/-- Its basis. -/
noncomputable def selBasis (P : Fin D.length → Prop) : Basis (SIdx D P) ℤ_[2] (selLat bM P) :=
  Basis.span (selVec_linIndep bM P)

theorem selBasis_apply (P : Fin D.length → Prop) (y : SIdx D P) :
    ((selBasis bM P y : selLat bM P) : V) = selVec bM P y :=
  congrArg Subtype.val (Basis.span_apply (selVec_linIndep bM P) y)

theorem selLat_le (P : Fin D.length → Prop) : selLat bM P ≤ M :=
  span_le.2 (by rintro _ ⟨y, rfl⟩; exact (bM _).2)

theorem selLat_fg (P : Fin D.length → Prop) : (selLat bM P).FG := fg_span (Set.finite_range _)

theorem finrank_selLat (P : Fin D.length → Prop) [DecidablePred P] :
    finrank ℤ_[2] (selLat bM P) = ∑ j ∈ univ.filter P, (D.get j).dim := by
  rw [finrank_eq_card_basis (selBasis bM P), Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact (Finset.sum_subtype (univ.filter P) (fun j => by simp) (fun j => (D.get j).dim)).symm

theorem bil_eq_zero_of_span {S T : Set V} (h : ∀ x ∈ S, ∀ y ∈ T, bil Q x y = 0) :
    ∀ x ∈ span ℤ_[2] S, ∀ y ∈ span ℤ_[2] T, bil Q x y = 0 := by
  intro x hx y hy
  refine span_induction (p := fun x _ => bil Q x y = 0) ?_ (by simp [bil]) ?_ ?_ hx
  · intro x hxS
    refine span_induction (p := fun y _ => bil Q x y = 0) (fun y hyT => h x hxS y hyT)
      (by simp [bil]) ?_ ?_ hy
    · intro a b _ _ ha hb
      rw [bil_comm, bil_add_left, bil_comm, ha, bil_comm, hb, add_zero]
    · intro r a _ ha
      rw [bil_comm, bil_rsmul_left, bil_comm, ha, mul_zero]
  · intro a b _ _ ha hb
    rw [bil_add_left, ha, hb, add_zero]
  · intro r a _ ha
    rw [bil_rsmul_left, ha, mul_zero]

variable (hG : ∀ x y, bil Q (bM x : V) (bM y : V) = bmat D x y)
include hG

/-- The Gram matrix of the blocks satisfying `P` is their block diagonal matrix. -/
theorem gram_sel (P : Fin D.length → Prop) :
    gram Q (fun y => (selBasis bM P y : V)) = blockDiagonal' fun j : {j // P j} => (D.get j.1).mat := by
  ext ⟨j₁, r⟩ ⟨j₂, s⟩
  simp only [OMeara.gram, of_apply, selBasis_apply, selVec, hG, bmat]
  by_cases h : j₁ = j₂
  · subst h; simp
  · rw [blockDiagonal'_apply_ne _ _ _ h, blockDiagonal'_apply_ne _ _ _ (fun h' => h (Subtype.ext h'))]

theorem bil_selVec_eq_zero {P P' : Fin D.length → Prop} (y : SIdx D P) (z : SIdx D P') (h : y.1.1 ≠ z.1.1) :
    bil Q (selVec bM P y) (selVec bM P' z) = 0 := by
  simp only [selVec, hG, bmat]
  exact blockDiagonal'_apply_ne _ _ _ h

theorem Q_selVec (P : Fin D.length → Prop) (y : SIdx D P) :
    Q (selVec bM P y) = (D.get y.1.1).mat y.2 y.2 := by
  rw [← bil_self, selVec, hG, bmat, blockDiagonal'_apply_eq]

/-! ### The Jordan components -/

variable (hD : ∀ b ∈ D, b.Valid) (hD0 : ∀ b ∈ D, 0 ≤ blockExp b)

omit hG in
theorem nonempty_sidx {k : ℕ} (h : ∃ j, bexp D j = k) : Nonempty (SIdx D fun j => bexp D j = k) := by
  obtain ⟨j, hj⟩ := h
  exact ⟨⟨⟨j, hj⟩, ⟨0, dyBlock_one_le_dim _⟩⟩⟩

include hD0 in
theorem gram_comp (k : ℕ) :
    gram Q (fun y => (selBasis bM (fun j => bexp D j = k) y : V)) =
      (2 : ℚ_[2]) ^ k • (blockDiagonal' fun j : {j // bexp D j = k} => bU (D.get j.1)).map
        (algebraMap ℤ_[2] ℚ_[2]) := by
  rw [gram_sel Q bM hG]
  ext ⟨j₁, r⟩ ⟨j₂, s⟩
  by_cases h : j₁ = j₂
  · subst h
    have hk : (blockExp (D.get j₁.1)).toNat = k := j₁.2
    simp only [blockDiagonal'_apply_eq, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    rw [mat_eq_smul _ (hD0 _ (List.get_mem _ _)), hk]
    simp
  · simp [blockDiagonal'_apply_ne _ _ _ h]

include hD hD0 in
theorem isModular_comp {k : ℕ} (hne : ∃ j, bexp D j = k) :
    IsModular Q (ℤ_[2] ∙ (2 : ℚ_[2]) ^ k) (selLat bM fun j => bexp D j = k) := by
  refine (isModular_iff_gram Q (selBasis bM _) (pow_ne_zero _ two_ne_zero)).2
    ⟨nonempty_sidx hne, _, ?_, gram_comp Q bM hG hD0 k⟩
  rw [det_blockDiagonal']
  exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
    fun j _ => isUnit_det_bU _ (hD _ (List.get_mem _ _))

include hD hD0 in
theorem scale_comp {k : ℕ} (hne : ∃ j, bexp D j = k) :
    scale Q (selLat bM fun j => bexp D j = k) = ℤ_[2] ∙ (2 : ℚ_[2]) ^ k :=
  (isModular_comp Q bM hG hD hD0 hne).2.1

variable {t : ℕ} (ks : Fin t → ℕ) (hks : StrictMono ks) (hrange : ∀ k, (∃ i, ks i = k) ↔ ∃ j, bexp D j = k)

/-- **The Jordan components**: the sublattices spanned by the blocks of exponent $k_i$. -/
def compLat (i : Fin t) : Submodule ℤ_[2] V := selLat bM fun j => bexp D j = ks i

include hD hD0 hks hrange in
/-- **The blocks of each exponent give a Jordan splitting** (O'Meara, §91C, p. 243). -/
theorem isJordanSplitting_comp : IsJordanSplitting Q M (compLat bM ks) := by
  have hne : ∀ i, ∃ j, bexp D j = ks i := fun i => (hrange (ks i)).1 ⟨i, rfl⟩
  have hmod : ∀ i, IsModular Q (ℤ_[2] ∙ (2 : ℚ_[2]) ^ ks i) (compLat bM ks i) :=
    fun i => isModular_comp Q bM hG hD hD0 (hne i)
  have hsc : ∀ i, scale Q (compLat bM ks i) = ℤ_[2] ∙ (2 : ℚ_[2]) ^ ks i :=
    fun i => scale_comp Q bM hG hD hD0 (hne i)
  have horth : ∀ i i', i ≠ i' → ∀ x ∈ compLat bM ks i, ∀ y ∈ compLat bM ks i', bil Q x y = 0 := by
    intro i i' hii'
    refine bil_eq_zero_of_span Q ?_
    rintro _ ⟨y, rfl⟩ _ ⟨z, rfl⟩
    refine bil_selVec_eq_zero Q bM hG y z fun h => hii' (hks.injective ?_)
    have h1 := y.1.2
    have h2 := z.1.2
    simp only at h1 h2
    rw [← h1, ← h2, h]
  refine ⟨⟨horth, iSupIndep_of_orth Q horth fun i => (hmod i).isRegular Q (selLat_fg bM _), ?_⟩,
    fun i => by rw [hsc i]; exact hmod i, fun i i' h => by show scale Q (compLat bM ks i') < scale Q (compLat bM ks i); rw [hsc, hsc]; exact span_two_pow_lt (hks h)⟩
  refine le_antisymm (iSup_le fun i => selLat_le bM _) ?_
  conv_lhs => rw [← span_basis_eq bM]
  refine span_le.2 ?_
  rintro _ ⟨x, rfl⟩
  obtain ⟨i, hi⟩ := (hrange (bexp D x.1)).2 ⟨x.1, rfl⟩
  exact Submodule.mem_iSup_of_mem i (subset_span ⟨⟨⟨x.1, hi.symm⟩, x.2⟩, rfl⟩)

omit hG in
theorem mat_sq_unit (b : DyBlock) (hv : b.Valid) (he : 0 ≤ blockExp b) (hb : IsSqBlock b) (r : Fin b.dim) :
    ∃ u : ℤ_[2], IsUnit u ∧ b.mat r r = (2 : ℚ_[2]) ^ (blockExp b).toNat * (u : ℚ_[2]) := by
  cases b with
  | sq e u =>
    have hu : Odd u := by
      simp only [DyBlock.Valid] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> decide
    refine ⟨(u : ℤ_[2]), Cassels.dyadic_isUnit_int_cast_of_odd hu, ?_⟩
    rw [mat_sq e u he]; simp [blockExp]
  | hyp e => exact absurd hb (by simp [IsSqBlock])
  | ell e => exact absurd hb (by simp [IsSqBlock])

include hD hD0 in
/-- **The norm of a Jordan component** is $2^{k+\delta}$. -/
theorem normIdeal_comp {k : ℕ} (hne : ∃ j, bexp D j = k) :
    normIdeal Q (selLat bM fun j => bexp D j = k) = ℤ_[2] ∙ (2 : ℚ_[2]) ^ (k + dlt (blockSymbol D) k) := by
  have hn := normIdeal_span (R := ℤ_[2]) Q (selVec bM fun j => bexp D j = k)
  change normIdeal Q (selLat bM _) = _ ⊔ (2 : ℚ_[2]) • scale Q (selLat bM _) at hn
  rw [hn, scale_comp Q bM hG hD hD0 hne, twoAdic_two_smul_span,
    show (2 : ℚ_[2]) * 2 ^ k = 2 ^ (k + 1) by ring]
  by_cases hI : IsTypeI (blockSymbol D) k
  · have hd : dlt (blockSymbol D) k = 0 := by simp [dlt, hI]
    rw [hd, add_zero]
    obtain ⟨j, hj, hsq⟩ := (isTypeI_blockSymbol D hD0 k).1 hI
    apply le_antisymm
    · refine sup_le (span_le.2 ?_) ((span_two_pow_le_iff _ _).2 (by omega))
      rintro _ ⟨y, rfl⟩
      dsimp only
      rw [Q_selVec Q bM hG, mat_eq_smul _ (hD0 _ (List.get_mem _ _))]
      have hk : (blockExp (D.get y.1.1)).toNat = k := y.1.2
      rw [hk]
      simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, PadicInt.algebraMap_apply]
      exact mem_span_two_pow k _
    · refine le_sup_of_le_left (span_le.2 ?_)
      rintro _ rfl
      obtain ⟨u, hu, hmat⟩ := mat_sq_unit (D.get j) (hD _ (List.get_mem _ _)) (hD0 _ (List.get_mem _ _)) hsq
        ⟨0, dyBlock_one_le_dim _⟩
      have hj' : (blockExp (D.get j)).toNat = k := hj
      rw [hj'] at hmat
      have hmem : Q (selVec bM (fun j => bexp D j = k) ⟨⟨j, hj⟩, ⟨0, dyBlock_one_le_dim _⟩⟩) ∈
          span ℤ_[2] (Set.range fun y => Q (selVec bM (fun j => bexp D j = k) y)) := subset_span ⟨_, rfl⟩
      rw [Q_selVec Q bM hG, hmat] at hmem
      have := Submodule.smul_mem _ (↑hu.unit⁻¹ : ℤ_[2]) hmem
      rwa [Algebra.smul_def, PadicInt.algebraMap_apply, mul_left_comm, ← PadicInt.coe_mul, hu.val_inv_mul,
        PadicInt.coe_one, mul_one] at this
  · have hd : dlt (blockSymbol D) k = 1 := by simp [dlt, hI]
    rw [hd]
    refine le_antisymm (sup_le (span_le.2 ?_) le_rfl) le_sup_right
    rintro _ ⟨y, rfl⟩
    have hns : ¬ IsSqBlock (D.get y.1.1) := fun h => hI ((isTypeI_blockSymbol D hD0 k).2 ⟨y.1.1, y.1.2, h⟩)
    obtain ⟨z, hz⟩ := mat_diag_binary (D.get y.1.1) (hD0 _ (List.get_mem _ _)) hns y.2
    have hk : (blockExp (D.get y.1.1)).toNat = k := y.1.2
    dsimp only
    rw [Q_selVec Q bM hG, hz, hk]
    exact mem_span_two_pow (k + 1) z

omit hG in
include hD0 in
theorem finrank_comp (k : ℕ) : finrank ℤ_[2] (selLat bM fun j => bexp D j = k) = (blockSymbol D k).dim := by
  rw [finrank_selLat, dim_blockSymbol D hD0]

omit hG in
include hks hrange in
/-- **The Jordan chain** $M_{(i)}$ is spanned by the blocks of exponent $\le k_i$. -/
theorem jordanChain_comp (i : Fin t) :
    jordanChain (compLat bM ks) i = selLat bM fun j => bexp D j ≤ ks i := by
  unfold jordanChain
  apply le_antisymm
  · refine iSup₂_le fun i' hi' => span_le.2 ?_
    rintro _ ⟨y, rfl⟩
    have hy : bexp D y.1.1 = ks i' := y.1.2
    exact subset_span ⟨⟨⟨y.1.1, by show bexp D y.1.1 ≤ ks i; rw [hy]; exact hks.monotone hi'⟩, y.2⟩, rfl⟩
  · refine span_le.2 ?_
    rintro _ ⟨y, rfl⟩
    obtain ⟨i', hi'⟩ := (hrange (bexp D y.1.1)).2 ⟨_, rfl⟩
    have hle : i' ≤ i := hks.le_iff_le.1 (by rw [hi']; exact y.1.2)
    exact Submodule.mem_iSup_of_mem i' (Submodule.mem_iSup_of_mem hle
      (subset_span ⟨⟨⟨y.1.1, hi'.symm⟩, y.2⟩, rfl⟩))

include hD0 in
/-- **The determinant of the chain**: $2^{E}\prod u_b$ over the blocks of exponent $\le k$. -/
theorem det_gram_chain (k : ℕ) :
    (gram Q fun y => (selBasis bM (fun j => bexp D j ≤ k) y : V)).det =
      (2 : ℚ_[2]) ^ (∑ j ∈ univ.filter (fun j => bexp D j ≤ k), bexp D j * (D.get j).dim) *
        (((∏ j ∈ univ.filter (fun j => bexp D j ≤ k), bUnit (D.get j) : ℤ)) : ℚ_[2]) := by
  rw [gram_sel Q bM hG, det_blockDiagonal',
    ← Finset.prod_subtype (univ.filter fun j => bexp D j ≤ k) (fun j => by simp) (fun j => (D.get j).mat.det),
    Finset.prod_congr rfl (fun j _ => det_mat (D.get j) (hD0 _ (List.get_mem _ _))), Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Int.cast_prod]
  rfl

omit hG in
include hD0 in
theorem chainExp_eq (k : ℕ) :
    ∑ j ∈ univ.filter (fun j => bexp D j ≤ k), bexp D j * (D.get j).dim =
      ∑ k' ∈ Finset.range (k + 1), k' * (blockSymbol D k').dim := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := bexp D) (t := Finset.range (k + 1))
    (fun j hj => by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj; simp; omega)]
  refine Finset.sum_congr rfl fun k' hk' => ?_
  rw [dim_blockSymbol D hD0, Finset.mul_sum, Finset.filter_filter]
  have hk'' : k' ≤ k := by simp at hk'; omega
  refine Finset.sum_congr (by ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega) ?_
  intro j hj
  simp only [Finset.mem_filter] at hj
  rw [hj.2]

/-- The weights of the blocks satisfying `P`, indexed by `Fin m`. -/
def selW (D : List DyBlock) (P : Fin D.length → Prop) [DecidablePred P]
    (i : Fin (Fintype.card (SIdx D P))) : ℤ :=
  bW (D.get ((Fintype.equivFin (SIdx D P)).symm i).1.1) ((Fintype.equivFin (SIdx D P)).symm i).2

omit hG in
theorem oddity_selW (P : Fin D.length → Prop) [DecidablePred P] :
    oddity (selW D P) = ∑ j ∈ univ.filter P, bOdd (D.get j) := by
  unfold oddity selW
  rw [Equiv.sum_comp (Fintype.equivFin (SIdx D P)).symm (fun y => oddityEntry (bW (D.get y.1.1) y.2)),
    Fintype.sum_sigma, Finset.sum_subtype (univ.filter P) (p := P) (fun j => by simp) (fun j => bOdd (D.get j))]
  rfl

omit hG in
theorem prod_selW (P : Fin D.length → Prop) [DecidablePred P] :
    ∏ i, selW D P i = ∏ j ∈ univ.filter P, ∏ r, bW (D.get j) r := by
  unfold selW
  rw [Equiv.prod_comp (Fintype.equivFin (SIdx D P)).symm (fun y => bW (D.get y.1.1) y.2), Fintype.prod_sigma,
    Finset.prod_subtype (univ.filter P) (p := P) (fun j => by simp) (fun j => ∏ r, bW (D.get j) r)]

include hD hD0 in
theorem rep_selW [FiniteDimensional ℚ_[2] V] (P : Fin D.length → Prop) [DecidablePred P] :
    D18.Rep (D18.subQ Q (selLat bM P)) (diagonal fun i => ((selW D P i : ℤ) : ℚ_[2])) := by
  set eqv := Fintype.equivFin (SIdx D P)
  set bA := (selBasis bM P).reindex eqv
  have hgA : (gram Q fun i => (bA i : V)) =
      (gram Q fun y => (selBasis bM P y : V)).submatrix eqv.symm eqv.symm := by
    ext i j; simp [OMeara.gram, bA, Basis.reindex_apply]
  have hdet : (gram Q fun i => (bA i : V)).det ≠ 0 := by
    rw [hgA, det_submatrix_equiv_self, gram_sel Q bM hG, det_blockDiagonal']
    refine Finset.prod_ne_zero_iff.2 fun j _ => ?_
    rw [det_mat _ (hD0 _ (List.get_mem _ _))]
    refine mul_ne_zero (pow_ne_zero _ two_ne_zero) ?_
    have h1 : bUnit (D.get j.1) ≠ 0 := fun h => by
      have := bUnit_odd (D.get j.1) (hD _ (List.get_mem _ _)); rw [h] at this; exact absurd this (by decide)
    exact_mod_cast h1
  obtain ⟨e, he⟩ := Resplit.exists_spanBasis Q bA hdet
  have h0 : D18.Rep (D18.subQ Q (selLat bM P)) (gram Q fun i => (bA i : V)) := ⟨e, he⟩
  set B := blockDiagonal' fun j : {j // P j} => bP (D.get j.1)
  have hPm : IsUnit (B.submatrix eqv.symm eqv.symm).det := by
    rw [det_submatrix_equiv_self, det_blockDiagonal', isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun j _ => bP_det_ne _
  have h1 := D18.rep_congr _ h0 hPm
  have hmat : B.submatrix eqv.symm eqv.symm * (gram Q fun i => (bA i : V)) * (B.submatrix eqv.symm eqv.symm)ᵀ =
      diagonal fun i => ((selW D P i : ℤ) : ℚ_[2]) := by
    rw [hgA, gram_sel Q bM hG, transpose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv]
    simp only [B]
    rw [blockDiagonal'_transpose, ← blockDiagonal'_mul, ← blockDiagonal'_mul,
      show (fun j : {j // P j} => bP (D.get j.1) * (D.get j.1).mat * (bP (D.get j.1))ᵀ) =
        fun j => diagonal fun r => ((bW (D.get j.1) r : ℤ) : ℚ_[2]) from
        funext fun j => bP_mul _ (hD0 _ (List.get_mem _ _)),
      blockDiagonal'_diagonal, submatrix_diagonal_equiv]
    rfl
  rwa [hmat] at h1

end Lattice

/-! ### O'Meara's conditions for two block lattices -/

/-- The exponent of $2$ in the product of the weights of a block. -/
def bWexp : DyBlock → ℕ
  | .sq e _ => e.toNat
  | .hyp e => 2 * (e.toNat + 1)
  | .ell e => 2 * (e.toNat + 1)

theorem prod_bW (b : DyBlock) : ∏ r, bW b r = 2 ^ bWexp b * bUnit b := by
  cases b with
  | sq e u =>
    show (∏ r : Fin 1, (![2 ^ e.toNat * u] : Fin 1 → ℤ) r) = _
    simp [bWexp, bUnit]
  | hyp e =>
    show (∏ r : Fin 2, (![2 ^ (e.toNat + 1) * 1, 2 ^ (e.toNat + 1) * (-1)] : Fin 2 → ℤ) r) = _
    simp [Fin.prod_univ_two, bWexp, bUnit]; ring
  | ell e =>
    show (∏ r : Fin 2, (![2 ^ (e.toNat + 1) * 1, 2 ^ (e.toNat + 1) * 3] : Fin 2 → ℤ) r) = _
    simp [Fin.prod_univ_two, bWexp, bUnit]; ring

theorem bWexp_mod_two (b : DyBlock) : bWexp b % 2 = ((blockExp b).toNat * b.dim) % 2 := by
  cases b <;> simp [bWexp, blockExp, DyBlock.dim] <;> omega

theorem bW_ne_zero (b : DyBlock) (hv : b.Valid) (r : Fin b.dim) : bW b r ≠ 0 := by
  have h := prod_bW b
  have hu := bUnit_odd b hv
  have hne : ∏ r, bW b r ≠ 0 := by
    rw [h]; refine mul_ne_zero (pow_ne_zero _ two_ne_zero) fun h0 => ?_
    rw [h0] at hu; exact absurd hu (by decide)
  exact (Finset.prod_ne_zero_iff.1 hne) r (Finset.mem_univ _)

theorem card_sidx (D : List DyBlock) (P : Fin D.length → Prop) [DecidablePred P] :
    Fintype.card (SIdx D P) = ∑ j ∈ univ.filter P, (D.get j).dim := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact (Finset.sum_subtype (univ.filter P) (p := P) (fun j => by simp) (fun j => (D.get j).dim)).symm

theorem chainDim_eq (D : List DyBlock) (hD0 : ∀ b ∈ D, 0 ≤ blockExp b) (k : ℕ) :
    ∑ j ∈ univ.filter (fun j => bexp D j ≤ k), (D.get j).dim =
      ∑ k' ∈ Finset.range (k + 1), (blockSymbol D k').dim := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := bexp D) (t := Finset.range (k + 1))
    (fun j hj => by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj; simp; omega)]
  refine Finset.sum_congr rfl fun k' hk' => ?_
  rw [dim_blockSymbol D hD0, Finset.filter_filter]
  have hk'' : k' ≤ k := by simp at hk'; omega
  exact Finset.sum_congr (by ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega) fun _ _ => rfl

theorem exists_bexp_iff (D : List DyBlock) (hD0 : ∀ b ∈ D, 0 ≤ blockExp b) (k : ℕ) :
    (∃ j, bexp D j = k) ↔ (blockSymbol D k).dim ≠ 0 := by
  rw [dim_blockSymbol D hD0, Ne, Finset.sum_eq_zero_iff]
  push Not
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, by simp [hj], by have := dyBlock_one_le_dim (D.get j); omega⟩
  · rintro ⟨j, hj, -⟩
    exact ⟨j, by simpa using hj⟩

/-- The nonzero-dimensional scales of a block decomposition. -/
def scaleSet (D : List DyBlock) : Finset ℕ := univ.image (bexp D)

/-- Their increasing enumeration. -/
def scaleEnum (D : List DyBlock) : Fin (scaleSet D).card ↪o ℕ := (scaleSet D).orderEmbOfFin rfl

theorem scaleEnum_range (D : List DyBlock) (k : ℕ) : (∃ i, scaleEnum D i = k) ↔ ∃ j, bexp D j = k := by
  have h := Finset.range_orderEmbOfFin (scaleSet D) rfl
  constructor
  · rintro ⟨i, rfl⟩
    have hmem : scaleEnum D i ∈ (scaleSet D : Set ℕ) := by rw [← h]; exact ⟨i, rfl⟩
    simpa [scaleSet] using hmem
  · intro hk
    have hmem : k ∈ (scaleSet D : Set ℕ) := by simpa [scaleSet] using hk
    rw [← h] at hmem
    exact hmem

theorem norm_two_zpow (u : ℤ) : ‖(2 : ℚ_[2]) ^ u‖ = (2 : ℝ)⁻¹ ^ u := by
  rw [norm_zpow, show ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ by simpa using Padic.norm_p (p := 2)]

theorem span_two_zpow_le {u v : ℤ} (h : (ℤ_[2] ∙ (2 : ℚ_[2]) ^ u) ≤ (ℤ_[2] ∙ (2 : ℚ_[2]) ^ v)) : v ≤ u := by
  rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  have h1 : ‖(2 : ℚ_[2]) ^ u‖ ≤ ‖(2 : ℚ_[2]) ^ v‖ := by
    rw [← hc, Algebra.smul_def, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one c)
  rw [norm_two_zpow, norm_two_zpow] at h1
  exact (zpow_le_zpow_iff_right_of_lt_one₀ (by norm_num) (by norm_num)).1 h1

theorem span_two_zpow_inj {u : ℤ} {n : ℕ} (h : (ℤ_[2] ∙ (2 : ℚ_[2]) ^ u) = ℤ_[2] ∙ (2 : ℚ_[2]) ^ n) : u = n := by
  rw [← zpow_natCast] at h
  exact le_antisymm (span_two_zpow_le h.ge) (span_two_zpow_le h.le)

theorem span_div_span {a b : ℚ_[2]} (hb : b ≠ 0) : (ℤ_[2] ∙ a) / (ℤ_[2] ∙ b) = ℤ_[2] ∙ (a / b) := by
  ext z
  rw [FIdealAux.mem_div_span_iff, Submodule.mem_span_singleton, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_⟩
    rw [Algebra.smul_def] at hr ⊢
    field_simp
    linear_combination hr
  · rintro ⟨r, rfl⟩
    refine ⟨r, ?_⟩
    rw [Algebra.smul_def, Algebra.smul_def]
    field_simp

theorem oddE_congr {u u' : ZMod 8} (h : 4 * u = 4 * u') (w : ZMod 8) : oddE u w = oddE u' w := by
  unfold oddE; rw [h]

section Classification

variable {V : Type*} [AddCommGroup V] [Module ℚ_[2] V] [Module ℤ_[2] V] [IsScalarTower ℤ_[2] ℚ_[2] V]
variable (Q : QuadraticForm ℚ_[2] V)
variable {D D' : List DyBlock} {L K : Submodule ℤ_[2] V} (bL : Basis (BIdx D) ℤ_[2] L) (bK : Basis (BIdx D') ℤ_[2] K)
  (hGL : ∀ x y, bil Q (bL x : V) (bL y : V) = bmat D x y) (hGK : ∀ x y, bil Q (bK x : V) (bK y : V) = bmat D' x y)
  (hD : ∀ b ∈ D, b.Valid) (hD0 : ∀ b ∈ D, 0 ≤ blockExp b) (hD' : ∀ b ∈ D', b.Valid)
  (hD'0 : ∀ b ∈ D', 0 ≤ blockExp b)
  (hshape : ∀ k, (blockSymbol D' k).dim = (blockSymbol D k).dim ∧ (blockSymbol D' k).type = (blockSymbol D k).type)

include hD0 hD'0 hshape in
theorem scaleEnum_range' (k : ℕ) : (∃ i, scaleEnum D i = k) ↔ ∃ j, bexp D' j = k := by
  rw [scaleEnum_range, exists_bexp_iff D hD0, exists_bexp_iff D' hD'0, (hshape k).1]

include hshape in
theorem dlt_eq (k : ℕ) : dlt (blockSymbol D') k = dlt (blockSymbol D) k := by
  have h : IsTypeI (blockSymbol D') k ↔ IsTypeI (blockSymbol D) k := by unfold IsTypeI; rw [(hshape k).2]
  unfold dlt; by_cases hI : IsTypeI (blockSymbol D) k
  · rw [if_pos hI, if_pos (h.2 hI)]
  · rw [if_neg hI, if_neg (fun h' => hI (h.1 h'))]

include hD0 in
theorem nextNZ_iff (k k' : ℕ) :
    NextNZ (blockSymbol D) k k' ↔
      ∃ i j : Fin (scaleSet D).card, (j : ℕ) = i + 1 ∧ scaleEnum D i = k ∧ scaleEnum D j = k' := by
  have hmem : ∀ k, (blockSymbol D k).dim ≠ 0 ↔ ∃ i, scaleEnum D i = k := fun k => by
    rw [scaleEnum_range, exists_bexp_iff D hD0]
  have hmono := (scaleEnum D).strictMono
  constructor
  · rintro ⟨hlt, hk, hk', hbetween⟩
    obtain ⟨i, rfl⟩ := (hmem k).1 hk
    obtain ⟨j, rfl⟩ := (hmem _).1 hk'
    have hij : i < j := hmono.lt_iff_lt.1 hlt
    refine ⟨i, j, ?_, rfl, rfl⟩
    by_contra hne
    have hlt' : (i : ℕ) + 1 < j := by have := Fin.lt_def.1 hij; omega
    set i' : Fin (scaleSet D).card := ⟨i + 1, by omega⟩
    have h1 : i < i' := Fin.lt_def.2 (by simp [i'])
    have h2 : i' < j := Fin.lt_def.2 (by simp [i']; omega)
    exact (hmem _).2 ⟨i', rfl⟩ (hbetween _ (hmono h1) (hmono h2))
  · rintro ⟨i, j, hij, rfl, rfl⟩
    have hlt : i < j := Fin.lt_def.2 (by omega)
    refine ⟨hmono hlt, (hmem _).2 ⟨i, rfl⟩, (hmem _).2 ⟨j, rfl⟩, fun x h1 h2 => ?_⟩
    by_contra hx
    obtain ⟨i', rfl⟩ := (hmem x).1 hx
    have a1 : i < i' := hmono.lt_iff_lt.1 h1
    have a2 : i' < j := hmono.lt_iff_lt.1 h2
    have := Fin.lt_def.1 a1
    have := Fin.lt_def.1 a2
    omega

theorem two_pow_ideal_eq {k k' δ δ' : ℕ} (h : k ≤ k') :
    (2 : ℚ_[2]) ^ (k + δ) * 2 ^ (k' + δ') / (2 ^ k * 2 ^ k) = 2 ^ (k' - k + δ + δ') := by
  rw [div_eq_iff (mul_ne_zero (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ two_ne_zero)), ← pow_add, ← pow_add,
    ← pow_add]
  congr 1; omega

include hGL hGK hD hD0 hD' hD'0 hshape in
/-- **Condition (i) of 93:29 for consecutive components $2^k$, $2^{k'}$ of two block lattices.** -/
theorem discQuot_iff {k k' : ℕ} (hkk : k < k') :
    DiscQuotSqEquivMod Q (selLat bL fun j => bexp D j ≤ k) (selLat bK fun j => bexp D' j ≤ k)
        (ℤ_[2] ∙ (2 : ℚ_[2]) ^ (k' - k + dlt (blockSymbol D) k + dlt (blockSymbol D) k')) ↔
      (2 ≤ k' - k + dlt (blockSymbol D) k + dlt (blockSymbol D) k' →
          2 * (unitPre (blockSymbol D) (k + 1) - unitPre (blockSymbol D') (k + 1)) = 0) ∧
        (3 ≤ k' - k + dlt (blockSymbol D) k + dlt (blockSymbol D) k' →
          unitPre (blockSymbol D) (k + 1) = unitPre (blockSymbol D') (k + 1)) := by
  set PL : Fin D.length → Prop := fun j => bexp D j ≤ k
  set PK : Fin D'.length → Prop := fun j => bexp D' j ≤ k
  set m := k' - k + dlt (blockSymbol D) k + dlt (blockSymbol D) k'
  have hm : 1 ≤ m := by omega
  set UL : ℤ := ∏ j ∈ univ.filter PL, bUnit (D.get j)
  set UK : ℤ := ∏ j ∈ univ.filter PK, bUnit (D'.get j)
  have hUL : Odd UL := Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one
    fun j _ => bUnit_odd _ (hD _ (List.get_mem _ _))
  have hUK : Odd UK := Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one
    fun j _ => bUnit_odd _ (hD' _ (List.get_mem _ _))
  have hE : ∑ j ∈ univ.filter PK, bexp D' j * (D'.get j).dim = ∑ j ∈ univ.filter PL, bexp D j * (D.get j).dim := by
    rw [chainExp_eq hD'0, chainExp_eq hD0]
    exact Finset.sum_congr rfl fun k'' _ => by rw [(hshape k'').1]
  set eA := Fintype.equivFinOfCardEq (finrank_eq_card_basis (selBasis bL PL)).symm
  set eB := Fintype.equivFinOfCardEq (finrank_eq_card_basis (selBasis bK PK)).symm
  set bA := (selBasis bL PL).reindex eA
  set bB := (selBasis bK PK).reindex eB
  have hdA : (gram Q fun i => (bA i : V)).det =
      (2 : ℚ_[2]) ^ (∑ j ∈ univ.filter PL, bexp D j * (D.get j).dim) * (UL : ℚ_[2]) := by
    rw [← det_gram_chain Q bL hGL hD0 k]
    rw [show (gram Q fun i => (bA i : V)) = (gram Q fun y => (selBasis bL PL y : V)).submatrix eA.symm eA.symm by
      ext i j; simp [OMeara.gram, bA, Basis.reindex_apply], det_submatrix_equiv_self]
  have hdB : (gram Q fun i => (bB i : V)).det =
      (2 : ℚ_[2]) ^ (∑ j ∈ univ.filter PL, bexp D j * (D.get j).dim) * (UK : ℚ_[2]) := by
    rw [← hE, ← det_gram_chain Q bK hGK hD'0 k]
    rw [show (gram Q fun i => (bB i : V)) = (gram Q fun y => (selBasis bK PK y : V)).submatrix eB.symm eB.symm by
      ext i j; simp [OMeara.gram, bB, Basis.reindex_apply], det_submatrix_equiv_self]
  have hUK0 : (UK : ℚ_[2]) ≠ 0 := by
    have : UK ≠ 0 := fun h => by rw [h] at hUK; exact absurd hUK (by decide)
    exact_mod_cast this
  have hBne : (gram Q fun i => (bB i : V)).det ≠ 0 := by
    rw [hdB]; exact mul_ne_zero (pow_ne_zero _ two_ne_zero) hUK0
  have hratio : (gram Q fun i => (bA i : V)).det / (gram Q fun i => (bB i : V)).det = (UL : ℚ_[2]) / UK := by
    rw [hdA, hdB]; field_simp
  have hcL : unitPre (blockSymbol D) (k + 1) = (UL : ZMod 8) := by
    rw [unitPre_blockSymbol D hD hD0, Int.cast_prod]
    exact Finset.prod_congr (by ext j; simp only [PL, Finset.mem_filter, Finset.mem_univ, true_and]; omega) fun _ _ => rfl
  have hcK : unitPre (blockSymbol D') (k + 1) = (UK : ZMod 8) := by
    rw [unitPre_blockSymbol D' hD' hD'0, Int.cast_prod]
    exact Finset.prod_congr (by ext j; simp only [PK, Finset.mem_filter, Finset.mem_univ, true_and]; omega) fun _ _ => rfl
  rw [hcL, hcK, ← two_pow_min_dvd_iff hm hUL hUK, ← sqEquivMod_iff hm hUL hUK]
  constructor
  · intro h
    have := Transfer28.discQuot_bases Q h bA bB hBne
    rwa [hratio] at this
  · intro h
    exact ⟨bA, bB, by rw [hratio]; exact h⟩

include hGL hGK hD hD0 hD' hD'0 hshape in
/-- **Condition (ii) of 93:29 for two block lattices, as an oddity equation.** -/
theorem spanRepresents_iff_oddity [FiniteDimensional ℚ_[2] V] (k : ℕ) (u : ℕ)
    (hAreg : IsRegular Q (selLat bL fun j => bexp D j ≤ k)) :
    SpanRepresents Q (selLat bL fun j => bexp D j ≤ k) (selLat bK fun j => bexp D' j ≤ k) ((2 : ℚ_[2]) ^ u) ↔
      oddPre (blockSymbol D) (k + 1) + oddE (u : ZMod 8) (unitPre (blockSymbol D) (k + 1) *
        unitPre (blockSymbol D') (k + 1)) = oddPre (blockSymbol D') (k + 1) + 1 := by
  set PL : Fin D.length → Prop := fun j => bexp D j ≤ k
  set PK : Fin D'.length → Prop := fun j => bexp D' j ≤ k
  have hcard : Fintype.card (SIdx D' PK) = Fintype.card (SIdx D PL) := by
    rw [card_sidx, card_sidx, chainDim_eq D' hD'0, chainDim_eq D hD0]
    exact Finset.sum_congr rfl fun k'' _ => (hshape k'').1
  set vA : Fin (Fintype.card (SIdx D PL)) → ℤ := selW D PL
  set vB : Fin (Fintype.card (SIdx D PL)) → ℤ := fun i => selW D' PK (Fin.cast hcard.symm i)
  have hvA : ∀ i, vA i ≠ 0 := fun i => bW_ne_zero _ (hD _ (List.get_mem _ _)) _
  have hvB : ∀ i, vB i ≠ 0 := fun i => bW_ne_zero _ (hD' _ (List.get_mem _ _)) _
  have hA := rep_selW Q bL hGL hD hD0 PL
  have hB : D18.Rep (D18.subQ Q (selLat bK PK)) (diagonal fun i => ((vB i : ℤ) : ℚ_[2])) := by
    obtain ⟨b, hb⟩ := rep_selW Q bK hGK hD' hD'0 PK
    refine ⟨b.reindex (finCongr hcard), ?_⟩
    ext i j
    have := congrFun (congrFun hb (Fin.cast hcard.symm i)) (Fin.cast hcard.symm j)
    simp only [OMeara.gram, of_apply, Basis.reindex_apply, finCongr_symm, finCongr_apply] at this ⊢
    rw [this]
    simp only [diagonal_apply, vB, Fin.cast_inj]
  rw [spanRepresents_iff_hasse Q hAreg (fun i => by exact_mod_cast hvA i) (fun i => by exact_mod_cast hvB i)
    hA hB (pow_ne_zero _ two_ne_zero), hasse_snoc_iff hvA hvB u]
  -- the oddities
  have hoA : oddity vA = oddPre (blockSymbol D) (k + 1) := by
    rw [oddity_selW, oddPre_blockSymbol D hD hD0]
    exact Finset.sum_congr (by ext j; simp only [PL, Finset.mem_filter, Finset.mem_univ, true_and]; omega) fun _ _ => rfl
  have hoB : oddity vB = oddPre (blockSymbol D') (k + 1) := by
    have : oddity vB = oddity (selW D' PK) := by
      unfold oddity
      exact Equiv.sum_comp (finCongr hcard.symm) (fun i => oddityEntry (selW D' PK i))
    rw [this, oddity_selW, oddPre_blockSymbol D' hD' hD'0]
    exact Finset.sum_congr (by ext j; simp only [PK, Finset.mem_filter, Finset.mem_univ, true_and]; omega) fun _ _ => rfl
  -- the products
  set EA := ∑ j ∈ univ.filter PL, bWexp (D.get j)
  set EB := ∑ j ∈ univ.filter PK, bWexp (D'.get j)
  set UL : ℤ := ∏ j ∈ univ.filter PL, bUnit (D.get j)
  set UK : ℤ := ∏ j ∈ univ.filter PK, bUnit (D'.get j)
  have hpA : ∏ i, vA i = 2 ^ EA * UL := by
    rw [prod_selW, Finset.prod_congr rfl fun j _ => prod_bW (D.get j), Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum]
  have hpB : ∏ i, vB i = 2 ^ EB * UK := by
    have : ∏ i, vB i = ∏ i, selW D' PK i := Equiv.prod_comp (finCongr hcard.symm) (fun i => selW D' PK i)
    rw [this, prod_selW, Finset.prod_congr rfl fun j _ => prod_bW (D'.get j), Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum]
  have hUL : Odd UL := Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one
    fun j _ => bUnit_odd _ (hD _ (List.get_mem _ _))
  have hUK : Odd UK := Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one
    fun j _ => bUnit_odd _ (hD' _ (List.get_mem _ _))
  have hparA : EA % 2 = (∑ j ∈ univ.filter PL, bexp D j * (D.get j).dim) % 2 := by
    rw [Finset.sum_nat_mod, Finset.sum_congr rfl fun j _ => bWexp_mod_two (D.get j), ← Finset.sum_nat_mod]; rfl
  have hparB : EB % 2 = (∑ j ∈ univ.filter PK, bexp D' j * (D'.get j).dim) % 2 := by
    rw [Finset.sum_nat_mod, Finset.sum_congr rfl fun j _ => bWexp_mod_two (D'.get j), ← Finset.sum_nat_mod]; rfl
  have hE : ∑ j ∈ univ.filter PK, bexp D' j * (D'.get j).dim = ∑ j ∈ univ.filter PL, bexp D j * (D.get j).dim := by
    rw [chainExp_eq hD'0, chainExp_eq hD0]
    exact Finset.sum_congr rfl fun k'' _ => by rw [(hshape k'').1]
  have hent : oddityEntry (2 ^ u * (∏ i, vB i) * ∏ i, vA i) =
      oddE (u : ZMod 8) (unitPre (blockSymbol D) (k + 1) * unitPre (blockSymbol D') (k + 1)) := by
    rw [hpA, hpB, show (2 : ℤ) ^ u * (2 ^ EB * UK) * (2 ^ EA * UL) = 2 ^ (u + EB + EA) * (UK * UL) by
      rw [pow_add, pow_add]; ring, oddityEntry_eq_oddE _ (hUK.mul hUL)]
    have hcL : unitPre (blockSymbol D) (k + 1) = (UL : ZMod 8) := by
      rw [unitPre_blockSymbol D hD hD0, Int.cast_prod]
      exact Finset.prod_congr (by ext j; simp only [PL, Finset.mem_filter, Finset.mem_univ, true_and]; omega) fun _ _ => rfl
    have hcK : unitPre (blockSymbol D') (k + 1) = (UK : ZMod 8) := by
      rw [unitPre_blockSymbol D' hD' hD'0, Int.cast_prod]
      exact Finset.prod_congr (by ext j; simp only [PK, Finset.mem_filter, Finset.mem_univ, true_and]; omega) fun _ _ => rfl
    rw [hcL, hcK, Int.cast_mul, mul_comm (UK : ZMod 8)]
    refine oddE_congr ?_ _
    exact four_mul_natCast_of_parity (by omega)
  rw [hoA, hoB, hent]

include hGL hGK hD hD0 hD' hD'0 hshape in
/-- **O'Meara's conditions (i), (ii) of 93:29 for two block lattices** are `OMPair` for all consecutive
nonzero-dimensional scales. -/
theorem cond29_iff [FiniteDimensional ℚ_[2] V] (hLfg : L.FG) :
    Cond29 Q (compLat bL (scaleEnum D)) (compLat bK (scaleEnum D)) ↔
      ∀ k k', NextNZ (blockSymbol D) k k' → OMPair (blockSymbol D) (blockSymbol D') k k' := by
  set ks := scaleEnum D
  have hrL := scaleEnum_range D
  have hrK := scaleEnum_range' hD0 hD'0 hshape
  have hJL := isJordanSplitting_comp Q bL hGL hD hD0 ks ks.strictMono hrL
  have hneL : ∀ i, ∃ j, bexp D j = ks i := fun i => (hrL _).1 ⟨i, rfl⟩
  have pair : ∀ i j : Fin (scaleSet D).card, (j : ℕ) = i + 1 →
      ((DiscQuotSqEquivMod Q (jordanChain (compLat bL ks) i) (jordanChain (compLat bK ks) i)
          (normIdeal Q (compLat bL ks i) * normIdeal Q (compLat bL ks j) /
            (scale Q (compLat bL ks i) * scale Q (compLat bL ks i))) ∧
        (normIdeal Q (compLat bL ks j) ≤ (4 : ℚ_[2]) • normIdeal Q (compLat bL ks i) →
          ∀ u : ℤ, ℤ_[2] ∙ ((2 : ℚ_[2]) ^ u) = normIdeal Q (compLat bL ks i) →
            SpanRepresents Q (jordanChain (compLat bL ks) i) (jordanChain (compLat bK ks) i) ((2 : ℚ_[2]) ^ u))) ↔
        OMPair (blockSymbol D) (blockSymbol D') (ks i) (ks j)) := by
    intro i j hij
    have hkk : ks i < ks j := ks.strictMono (Fin.lt_def.2 (by omega))
    have hAreg : IsRegular Q (selLat bL fun j => bexp D j ≤ ks i) := by
      rw [← jordanChain_comp bL ks ks.strictMono hrL i]; exact isRegular_jordanChain Q hLfg hJL i
    have hnLi : normIdeal Q (compLat bL ks i) = ℤ_[2] ∙ (2 : ℚ_[2]) ^ (ks i + dlt (blockSymbol D) (ks i)) :=
      normIdeal_comp Q bL hGL hD hD0 (hneL i)
    have hnLj : normIdeal Q (compLat bL ks j) = ℤ_[2] ∙ (2 : ℚ_[2]) ^ (ks j + dlt (blockSymbol D) (ks j)) :=
      normIdeal_comp Q bL hGL hD hD0 (hneL j)
    have hsLi : scale Q (compLat bL ks i) = ℤ_[2] ∙ (2 : ℚ_[2]) ^ ks i := scale_comp Q bL hGL hD hD0 (hneL i)
    rw [hnLi, hnLj, hsLi, jordanChain_comp bL ks ks.strictMono hrL i, jordanChain_comp bK ks ks.strictMono hrK i,
      FIdealAux.span_mul_span', FIdealAux.span_mul_span', span_div_span (mul_ne_zero (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ two_ne_zero)),
      two_pow_ideal_eq hkk.le, FIdealAux.smul_span_singleton,
      show (4 : ℚ_[2]) * 2 ^ (ks i + dlt (blockSymbol D) (ks i)) =
        2 ^ (ks i + dlt (blockSymbol D) (ks i) + 2) by ring, span_two_pow_le_iff]
    unfold OMPair
    rw [← and_assoc, discQuot_iff Q bL bK hGL hGK hD hD0 hD' hD'0 hshape hkk]
    refine and_congr Iff.rfl (imp_congr (by omega) ?_)
    rw [← spanRepresents_iff_oddity Q bL bK hGL hGK hD hD0 hD' hD'0 hshape (ks i) _ hAreg]
    constructor
    · intro h; exact zpow_natCast (2 : ℚ_[2]) _ ▸ h _ (by rw [zpow_natCast])
    · intro h u hu
      obtain rfl := span_two_zpow_inj hu
      rwa [zpow_natCast]
  unfold Cond29
  constructor
  · intro h k k' hk
    obtain ⟨i, j, hij, rfl, rfl⟩ := (nextNZ_iff hD0 k k').1 hk
    exact (pair i j hij).1 (h i j hij)
  · intro h i j hij
    exact (pair i j hij).2 (h _ _ ((nextNZ_iff hD0 _ _).2 ⟨i, j, hij, rfl, rfl⟩))

include hGL hGK hD hD0 hD' hD'0 hshape in
/-- **The class of a block lattice by O'Meara's 93:29**: two lattices on a regular quadratic space over $\mathbb Q_2$,
with bases in which their Gram matrices are block diagonal matrices of Cassels blocks of the same dimensions and types
at each scale, are in the same class iff `OMPair` holds for all consecutive nonzero-dimensional scales. -/
@[kb "omeara1963" "§93G, 93:29, p. 277 (lattices of 2-adic block decompositions)"]
theorem cls_eq_iff_omPair [FiniteDimensional ℚ_[2] V] (hQ : (QuadraticMap.associated Q).Nondegenerate)
    [L.IsLattice ℚ_[2]] [K.IsLattice ℚ_[2]] :
    cls Q L = cls Q K ↔
      ∀ k k', NextNZ (blockSymbol D) k k' → OMPair (blockSymbol D) (blockSymbol D') k k' := by
  set ks := scaleEnum D
  have hrL := scaleEnum_range D
  have hrK := scaleEnum_range' hD0 hD'0 hshape
  have hJL := isJordanSplitting_comp Q bL hGL hD hD0 ks ks.strictMono hrL
  have hJK := isJordanSplitting_comp Q bK hGK hD' hD'0 ks ks.strictMono hrK
  have hneL : ∀ i, ∃ j, bexp D j = ks i := fun i => (hrL _).1 ⟨i, rfl⟩
  have hneK : ∀ i, ∃ j, bexp D' j = ks i := fun i => (hrK _).1 ⟨i, rfl⟩
  have hJ : SameJordanInvariants Q Q (compLat bL ks) (compLat bK ks) := by
    refine ⟨rfl, fun i => ?_⟩
    simp only [Fin.cast_eq_self]
    refine ⟨?_, ?_, ?_⟩
    · show finrank ℤ_[2] (selLat bL _) = finrank ℤ_[2] (selLat bK _)
      rw [finrank_comp bL hD0, finrank_comp bK hD'0, (hshape _).1]
    · show scale Q (selLat bL _) = scale Q (selLat bK _)
      rw [scale_comp Q bL hGL hD hD0 (hneL i), scale_comp Q bK hGK hD' hD'0 (hneK i)]
    · show normIdeal Q (selLat bL _) = normIdeal Q (selLat bK _)
      rw [normIdeal_comp Q bL hGL hD hD0 (hneL i), normIdeal_comp Q bK hGK hD' hD'0 (hneK i),
        dlt_eq hshape]
  have h29 := (G29.twoAdicClassificationLe_twoAdic (R := ℤ_[2]) Q
    (PadicClass.localHilbertField_padic 2)).cls_eq_iff PadicInt.irreducible_p hQ L K _ _ hJL hJK hJ
  rw [h29]
  exact cond29_iff Q bL bK hGL hGK hD hD0 hD' hD'0 hshape (Submodule.IsLattice.fg (A := ℚ_[2]))

end Classification

end QuadFormsKB.ConwaySloane.TwoAdic

end
