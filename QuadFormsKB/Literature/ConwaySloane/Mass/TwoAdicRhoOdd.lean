/-
# The proportion $\rho$ when the unimodular constituent is odd of odd dimension

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), (3), p. 263, Table 1, p. 264 (bibliography key `conwaysloane1988`).

For $U = \langle u\rangle \perp E$ ($E$ even unimodular) and $M = E \perp 2B$, splitting off $\langle u\rangle$
(`alphaP_blk_odd`) gives $\rho(U, B) = \rho_{\langle u\rangle}(E \perp 2B)\,\rho(E, B)/\rho_{\langle u\rangle}(E)$.
For a one-dimensional odd part the condition on $w$ is explicit: $Mw \equiv 0 \pmod 2$ and
$w^{\mathsf T}Mw \equiv 0 \pmod 8$ (`goodO_one_iff`). Indices are 0-based.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicRhoEven
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicOddSplit

set_option linter.unusedSectionVars false

namespace QuadFormsKB.ConwaySloane.Mass.Two

open Matrix QuadFormsKB.Cassels QuadFormsKB.ConwaySloane

variable {b : ℕ}

/-! ### The condition for a one-dimensional odd part -/

theorem zmod8_unit_sq {g : ZMod (2 ^ 3)} (hg : IsUnit g) : g * g = 1 := by
  have : ∀ x : ZMod (2 ^ 3), IsUnit x → x * x = 1 := by decide
  exact this g hg

/-- For $O = (u)$ with $u$ odd: $O + (k) \sim O$ over $\mathbb Z_2$ iff $8 \mid k$. -/
theorem zpEquiv_one_iff {O K : Matrix (Fin 1) (Fin 1) ℤ} (hO : ¬ 2 ∣ O 0 0) :
    ZpEquiv (O.map (Int.cast : ℤ → ℚ_[2])) ((O + K).map (Int.cast : ℤ → ℚ_[2])) ↔ (8 : ℤ) ∣ K 0 0 := by
  have hdet : ¬ 2 ∣ O.det := by rwa [Matrix.det_fin_one]
  constructor
  · intro h
    obtain ⟨G, hG, hGe⟩ := exists_unit_congr_of_zpEquiv (p := 2) h 3
    have hG0 : IsUnit (G 0 0) := by
      have := (Matrix.isUnit_iff_isUnit_det G).mp hG
      rwa [Matrix.det_fin_one] at this
    have e := congrArg (fun X => X 0 0) hGe
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_one, Matrix.map_apply,
      Matrix.add_apply, map_add] at e
    have e2 : (G 0 0 * G 0 0) * ((O 0 0 : ℤ) : ZMod (2 ^ 3)) = (O 0 0 : ZMod (2 ^ 3)) + (K 0 0 : ZMod (2 ^ 3)) := by
      simp only [Int.coe_castRingHom] at e; rw [← e]; ring
    rw [zmod8_unit_sq hG0, one_mul] at e2
    have hk : ((K 0 0 : ℤ) : ZMod (2 ^ 3)) = 0 := by
      have := congrArg (fun z => z - ((O 0 0 : ℤ) : ZMod (2 ^ 3))) e2
      simpa using this.symm
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (K 0 0) (2 ^ 3)).mp hk
    simpa using this
  · intro h
    have hOs : Oᵀ = O := by ext i j; fin_cases i; fin_cases j; rfl
    have hKs : (O + K)ᵀ = O + K := by ext i j; fin_cases i; fin_cases j; rfl
    refine dyadic_zpEquiv_of_int O (O + K) 1 hOs hKs
      (Int.not_even_iff_odd.mp fun he => hdet (even_iff_two_dvd.mp he)) (by simp) fun i j => ?_
    fin_cases i; fin_cases j
    simp only [transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.add_apply]
    obtain ⟨c, hc⟩ := h
    exact ⟨-c, by simp [hc]⟩

/-- **The condition of `GoodO` for a one-dimensional odd part** $O = (u)$: $Mw \equiv 0 \pmod 2$ and
$w^{\mathsf T}Mw \equiv 0 \pmod 8$. -/
theorem goodO_one_iff {O : Matrix (Fin 1) (Fin 1) ℤ} (hO : ¬ 2 ∣ O 0 0) {M : Matrix (Fin b) (Fin b) ℤ}
    (hMs : Mᵀ = M) (W : Matrix (Fin b) (Fin 1) ℤ) :
    GoodO O M W ↔ (∀ i, 2 ∣ (M * W) i 0) ∧ (8 : ℤ) ∣ (Wᵀ * M * W) 0 0 := by
  unfold GoodO GoodO1
  rw [zpEquiv_one_iff hO, and_comm]
  refine and_congr_left' ?_
  rw [Matrix.adjugate_subsingleton, Matrix.mul_one]
  have e : ∀ i, (M * W * Wᵀ * M) i i = (M * W) i 0 * (M * W) i 0 := fun i => by
    rw [Matrix.mul_assoc, Matrix.mul_apply, Fin.sum_univ_one]
    congr 1
    rw [show (Wᵀ * M) 0 i = (Mᵀ * W) i 0 by
      simp [Matrix.mul_apply, Matrix.transpose_apply, mul_comm], hMs]
  refine forall_congr' fun i => ?_
  rw [e]
  exact ⟨fun h => (Int.prime_two.dvd_mul.mp h).elim id id, fun h => h.mul_right _⟩

/-! ### The structured second block $M = E \perp 2B$ -/

section Blk

variable {e : ℕ} (E : Matrix (Fin e) (Fin e) ℤ) (B : Matrix (Fin b) (Fin b) ℤ) (W : Matrix (Fin (e + b)) (Fin 1) ℤ)

theorem blk_mul_castAdd (k : Fin e) :
    (blk 2 E B * W) (Fin.castAdd b k) 0 = (E * W.submatrix (Fin.castAdd b) id) k 0 := by
  simp [blk, Matrix.mul_apply, Fin.sum_univ_add]

theorem blk_mul_natAdd (k : Fin b) :
    (blk 2 E B * W) (Fin.natAdd e k) 0 = 2 * (B * W.submatrix (Fin.natAdd e) id) k 0 := by
  simp only [blk, Matrix.mul_apply, Fin.sum_univ_add, submatrix_apply, Function.comp, id,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
    Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast; ring

theorem quad_blk :
    (Wᵀ * blk 2 E B * W) 0 0 = ((W.submatrix (Fin.castAdd b) id)ᵀ * E * W.submatrix (Fin.castAdd b) id) 0 0 +
      2 * ((W.submatrix (Fin.natAdd e) id)ᵀ * B * W.submatrix (Fin.natAdd e) id) 0 0 := by
  simp only [blk, Matrix.mul_apply, Fin.sum_univ_add, submatrix_apply, Function.comp, id, transpose_apply,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, mul_zero, Finset.sum_const_zero, zero_add,
    add_zero, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Blk

theorem two_dvd_of_mul_unimod {e : ℕ} {E : Matrix (Fin e) (Fin e) ℤ} (hEd : ¬ 2 ∣ E.det) {Y : Matrix (Fin e) (Fin 1) ℤ}
    (h : ∀ k, 2 ∣ (E * Y) k 0) : ∀ k, 2 ∣ Y k 0 := by
  have hu : IsUnit (E.map (Int.castRingHom (ZMod 2))).det := by
    rw [show (E.map (Int.castRingHom (ZMod 2))).det = ((E.det : ℤ) : ZMod 2) from
      (RingHom.map_det (Int.castRingHom (ZMod 2)) E).symm]
    have : ((E.det : ℤ) : ZMod 2) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hEd
    exact (isUnit_iff_ne_zero).mpr this
  have h0 : E.map (Int.castRingHom (ZMod 2)) * Y.map (Int.castRingHom (ZMod 2)) = 0 := by
    rw [← Matrix.map_mul]; ext k j; fin_cases j
    simp only [Matrix.map_apply, Matrix.zero_apply, eq_intCast]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h k
  have hY : Y.map (Int.castRingHom (ZMod 2)) = 0 := by
    have := congrArg (fun X => (E.map (Int.castRingHom (ZMod 2)))⁻¹ * X) h0
    rwa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul, Matrix.mul_zero] at this
  intro k
  have := congrFun (congrFun hY k) 0
  simp only [Matrix.map_apply, Matrix.zero_apply, eq_intCast] at this
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp this

theorem eight_dvd_quad_even {e : ℕ} {E : Matrix (Fin e) (Fin e) ℤ} (hEs : Eᵀ = E) (hEe : EvenDiag E)
    {Y : Matrix (Fin e) (Fin 1) ℤ} (h : ∀ k, 2 ∣ Y k 0) : (8 : ℤ) ∣ (Yᵀ * E * Y) 0 0 := by
  obtain ⟨Y', hY'⟩ : ∃ Y' : Matrix (Fin e) (Fin 1) ℤ, Y = (2 : ℤ) • Y' := by
    refine ⟨Matrix.of fun k j => Y k j / 2, ?_⟩
    ext k j
    rw [Subsingleton.elim j 0]
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [Int.mul_ediv_cancel' (h k)]
  have hq := diag_quad hEs hEe Y' 0
  have e4 : Yᵀ * E * Y = (4 : ℤ) • (Y'ᵀ * E * Y') := by
    rw [hY', transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]; norm_num
  rw [e4, Matrix.smul_apply, hq, smul_eq_mul]
  exact ⟨(Y'ᵀ * halfUp E * Y') 0 0, by ring⟩

/-- **The condition for $O = (u)$ and $M = E \perp 2B$**: the rows of $W$ over $E$ are even, and
$w_B^{\mathsf T}Bw_B \equiv 0 \pmod 4$. -/
theorem goodO_blk_iff {O : Matrix (Fin 1) (Fin 1) ℤ} (hO : ¬ 2 ∣ O 0 0) {e : ℕ} {E : Matrix (Fin e) (Fin e) ℤ}
    (hEs : Eᵀ = E) (hEe : EvenDiag E) (hEd : ¬ 2 ∣ E.det) {B : Matrix (Fin b) (Fin b) ℤ} (hBs : Bᵀ = B)
    (W : Matrix (Fin (e + b)) (Fin 1) ℤ) :
    GoodO O (blk 2 E B) W ↔ (∀ k, 2 ∣ W (Fin.castAdd b k) 0) ∧
      (4 : ℤ) ∣ ((W.submatrix (Fin.natAdd e) id)ᵀ * B * W.submatrix (Fin.natAdd e) id) 0 0 := by
  have hMs : (blk 2 E B)ᵀ = blk 2 E B := (blk_isSymm (p := 2) (show E.IsSymm from hEs) (show B.IsSymm from hBs)).eq
  rw [goodO_one_iff hO hMs, quad_blk]
  have hcol : (∀ i, 2 ∣ (blk 2 E B * W) i 0) ↔ ∀ k, 2 ∣ W (Fin.castAdd b k) 0 := by
    constructor
    · intro h
      have := two_dvd_of_mul_unimod hEd (Y := W.submatrix (Fin.castAdd b) id) fun k => by
        rw [← blk_mul_castAdd E B W k]; exact h _
      exact this
    · intro h i
      refine Fin.addCases (fun k => ?_) (fun k => ?_) i
      · rw [blk_mul_castAdd, Matrix.mul_apply]
        exact Finset.dvd_sum fun j _ => (h j).mul_left _
      · rw [blk_mul_natAdd]; exact dvd_mul_right _ _
  rw [hcol]
  refine and_congr_right fun h => ?_
  have h8 := eight_dvd_quad_even hEs hEe (Y := W.submatrix (Fin.castAdd b) id) h
  constructor
  · intro h'
    have := (dvd_add_right h8).mp h'
    obtain ⟨c, hc⟩ := this
    exact ⟨c, by linarith⟩
  · intro ⟨c, hc⟩
    exact dvd_add h8 ⟨c, by rw [hc]; ring⟩

/-! ### Counting -/

/-- $p_B$: the proportion of $z \in (\mathbb Z/8)^b$ with $z^{\mathsf T}Bz \equiv 0 \pmod 4$. -/
noncomputable def pB (B : Matrix (Fin b) (Fin b) ℤ) : ℝ :=
  (Nat.card {z : Matrix (Fin b) (Fin 1) (ZMod (2 ^ 3)) // (4 : ℤ) ∣ ((lift z)ᵀ * B * lift z) 0 0} : ℝ) / 8 ^ b

/-- The even columns. -/
def EvenCol {e : ℕ} (Y : Matrix (Fin e) (Fin 1) (ZMod (2 ^ 3))) : Prop := ∀ k, 2 ∣ lift Y k 0

theorem goodO_E_iff {O : Matrix (Fin 1) (Fin 1) ℤ} (hO : ¬ 2 ∣ O 0 0) {e : ℕ} {E : Matrix (Fin e) (Fin e) ℤ}
    (hEs : Eᵀ = E) (hEe : EvenDiag E) (hEd : ¬ 2 ∣ E.det) (W : Matrix (Fin e) (Fin 1) ℤ) :
    GoodO O E W ↔ ∀ k, 2 ∣ W k 0 := by
  rw [goodO_one_iff hO hEs]
  refine ⟨fun h => two_dvd_of_mul_unimod hEd h.1, fun h => ⟨fun k => ?_, eight_dvd_quad_even hEs hEe h⟩⟩
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun j _ => (h j).mul_left _

/-- The splitting of a column over $E \perp 2B$. -/
def colSplit (e : ℕ) : Matrix (Fin (e + b)) (Fin 1) (ZMod (2 ^ 3)) ≃
    Matrix (Fin e) (Fin 1) (ZMod (2 ^ 3)) × Matrix (Fin b) (Fin 1) (ZMod (2 ^ 3)) :=
  (finSumFinEquiv.arrowCongr (Equiv.refl _)).symm.trans (Equiv.sumArrowEquivProdArrow _ _ _)

theorem card_goodO_blk {O : Matrix (Fin 1) (Fin 1) ℤ} (hO : ¬ 2 ∣ O 0 0) {e : ℕ} {E : Matrix (Fin e) (Fin e) ℤ}
    (hEs : Eᵀ = E) (hEe : EvenDiag E) (hEd : ¬ 2 ∣ E.det) {B : Matrix (Fin b) (Fin b) ℤ} (hBs : Bᵀ = B) :
    Nat.card {W : Matrix (Fin (e + b)) (Fin 1) (ZMod (2 ^ 3)) // GoodO O (blk 2 E B) (lift W)} =
      Nat.card {Y : Matrix (Fin e) (Fin 1) (ZMod (2 ^ 3)) // EvenCol Y} *
      Nat.card {z : Matrix (Fin b) (Fin 1) (ZMod (2 ^ 3)) // (4 : ℤ) ∣ ((lift z)ᵀ * B * lift z) 0 0} := by
  rw [← Nat.card_prod, ← Nat.card_congr (Equiv.subtypeProdEquivProd)]
  refine Nat.card_congr (Equiv.subtypeEquiv (colSplit e) fun W => ?_)
  rw [goodO_blk_iff hO hEs hEe hEd hBs]
  rfl

theorem card_goodO_E {O : Matrix (Fin 1) (Fin 1) ℤ} (hO : ¬ 2 ∣ O 0 0) {e : ℕ} {E : Matrix (Fin e) (Fin e) ℤ}
    (hEs : Eᵀ = E) (hEe : EvenDiag E) (hEd : ¬ 2 ∣ E.det) :
    Nat.card {W : Matrix (Fin e) (Fin 1) (ZMod (2 ^ 3)) // GoodO O E (lift W)} =
      Nat.card {Y : Matrix (Fin e) (Fin 1) (ZMod (2 ^ 3)) // EvenCol Y} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun W => goodO_E_iff hO hEs hEe hEd _)

/-- **$\rho_{(u)}(E \perp 2B) = \rho_{(u)}(E)\,p_B$.** -/
theorem rhoO_blk {O : Matrix (Fin 1) (Fin 1) ℤ} (hO : ¬ 2 ∣ O 0 0) {e : ℕ} {E : Matrix (Fin e) (Fin e) ℤ}
    (hEs : Eᵀ = E) (hEe : EvenDiag E) (hEd : ¬ 2 ∣ E.det) {B : Matrix (Fin b) (Fin b) ℤ} (hBs : Bᵀ = B) :
    rhoO O (blk 2 E B) = rhoO O E * pB B := by
  unfold rhoO pB
  rw [card_goodO_blk hO hEs hEe hEd hBs, card_goodO_E hO hEs hEe hEd]
  push_cast
  rw [show (e + b) * 1 = e * 1 + b by ring, pow_add]
  field_simp

theorem rhoO_blk' {a : ℕ} (ha : a = 1) {O : Matrix (Fin a) (Fin a) ℤ} (hO : ∀ i, ¬ 2 ∣ O i i) {e : ℕ}
    {E : Matrix (Fin e) (Fin e) ℤ} (hEs : Eᵀ = E) (hEe : EvenDiag E) (hEd : ¬ 2 ∣ E.det)
    {B : Matrix (Fin b) (Fin b) ℤ} (hBs : Bᵀ = B) : rhoO O (blk 2 E B) = rhoO O E * pB B := by
  subst ha; exact rhoO_blk (hO 0) hEs hEe hEd hBs

/-! ### The formula $\rho(\langle u\rangle \perp E, B) = p_B\,\rho(E, B)$ -/

theorem alphaP_reidx {m n : ℕ} {M : Matrix (Fin m) (Fin m) ℤ} {N : Matrix (Fin n) (Fin n) ℤ} (h : Reidx M N) :
    alphaP 2 M = alphaP 2 N := by
  obtain ⟨e, rfl⟩ := h
  obtain rfl : m = n := by simpa using Fintype.card_congr e
  have hZ : ZpEquiv (N.map (Int.cast : ℤ → ℚ_[2])) ((N.submatrix e e).map (Int.cast : ℤ → ℚ_[2])) := by
    rw [← Matrix.submatrix_map]; exact dyadic_zpEquiv_perm _ e
  exact alphaP_eq_of_zpEquiv hZ

theorem blk_eq_orthSum {a c : ℕ} (p : ℕ) (U : Matrix (Fin a) (Fin a) ℤ) (C : Matrix (Fin c) (Fin c) ℤ) :
    blk p U C = orthSumMat U ((p : ℤ) • C) := by
  rw [blk, dyadic_orthSumMat_eq]

theorem one_smul_int {c : ℕ} (C : Matrix (Fin c) (Fin c) ℤ) : (((1 : ℕ) : ℤ) • C) = C := by simp

/-- **$\rho(\langle u\rangle \perp E, B) = p_B\,\rho(E, B)$** for $E$ a list of blocks $2xy$,
$2x^2 + 2xy + 2y^2$ of exponent $0$, splitting off $\langle u\rangle$ from $U \perp 2B$ and from $U$. -/
@[kb "conwaysloane1988" "(3), p. 263 (p = 2, splitting off a one-dimensional odd part)"]
theorem rho_sq_cons {u : ℤ} (hu : u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7) {L : List DyBlock}
    (hL : ∀ c ∈ L, blockExp c = 0 ∧ ¬ IsSqBlock c) {B : Matrix (Fin b) (Fin b) ℤ} (hBs : B.IsSymm)
    (hB : B.det ≠ 0) :
    rho (intMat (DyBlock.sq 0 u :: L)) B = pB B * rho (intMat L) B := by
  have hvL : ∀ c ∈ L, c.Valid := fun c hc => by
    cases c with
    | sq e v => exact absurd trivial (hL _ hc).2
    | hyp e => trivial
    | ell e => trivial
  have heL : ∀ c ∈ L, blockExp c = 0 := fun c hc => (hL c hc).1
  set E := intMat L
  have hEs : Eᵀ = E := (isSymm_intMat L).eq
  have hEe : EvenDiag E := evenDiag_intMat L (fun c hc => (heL c hc).ge) fun c hc hh => (hL c hc).2 hh.1
  have hEd : ¬ 2 ∣ E.det := det_odd_of_zero hvL heL
  set O := intMat [DyBlock.sq 0 u]
  have hvO : ∀ c ∈ [DyBlock.sq 0 u], c.Valid := by
    intro c hc; rw [List.mem_singleton] at hc; subst hc; exact hu
  have heO : ∀ c ∈ [DyBlock.sq 0 u], blockExp c = 0 := by simp [blockExp]
  have key : ∀ i j, O i j = u := by
    intro i j
    show orthSumMat (bInt (DyBlock.sq 0 u)) (intMat []) i j = u
    refine Fin.addCases (fun i' => ?_) (fun i' => i'.elim0) i
    refine Fin.addCases (fun j' => ?_) (fun j' => j'.elim0) j
    rw [orthSumMat_cc]
    have hi : i' = ⟨0, Nat.one_pos⟩ := Fin.ext (by have := i'.isLt; simp [DyBlock.dim] at this; omega)
    have hj : j' = ⟨0, Nat.one_pos⟩ := Fin.ext (by have := j'.isLt; simp [DyBlock.dim] at this; omega)
    subst hi hj
    show (2 : ℤ) ^ (0 : ℤ).toNat * u = u; simp
  have hOd : ∀ i, ¬ 2 ∣ O i i := fun i => by rw [key]; exact valid_odd hu
  have hO2 : O.map (Int.castRingHom (ZMod 2)) = 1 := by
    ext i j
    have hij : i = j := Fin.ext (by have := i.isLt; have := j.isLt; simp [dyDim, DyBlock.dim] at *; omega)
    subst hij
    simp only [Matrix.map_apply, eq_intCast, Matrix.one_apply_eq, key]
    rcases hu with rfl | rfl | rfl | rfl <;> rfl
  have hv : ∀ c ∈ DyBlock.sq 0 u :: L, c.Valid := by
    intro c hc; rcases List.mem_cons.mp hc with rfl | h
    · exact hu
    · exact hvL c h
  have he : ∀ c ∈ DyBlock.sq 0 u :: L, blockExp c = 0 := by
    intro c hc; rcases List.mem_cons.mp hc with rfl | h
    · rfl
    · exact heL c h
  have hMs : (blk 2 E B).IsSymm := blk_isSymm (p := 2) (isSymm_intMat L) hBs
  have hMe : EvenDiag (blk 2 E B) := by
    intro i
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i
    · simp only [blk, submatrix_apply, finSumFinEquiv_symm_apply_castAdd, fromBlocks_apply₁₁]; exact hEe k
    · simp only [blk, submatrix_apply, finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₂₂, Matrix.smul_apply,
        smul_eq_mul]
      exact ⟨B k k, by push_cast; ring⟩
  have hM0 : (blk 2 E B).det ≠ 0 := by
    rw [blk_det]; exact mul_ne_zero (fun h => hEd (h ▸ dvd_zero _)) (mul_ne_zero (pow_ne_zero _ (by norm_num)) hB)
  have ha : dyDim [DyBlock.sq 0 u] = 1 ∨ dyDim [DyBlock.sq 0 u] = 2 := Or.inl rfl
  -- the three densities
  have h1 := alphaP_blk_odd hvO heO ha hO2 hMs hMe hM0
  have h2 := alphaP_blk_two_rho hvL heL hBs hB
  have hEsym : E.IsSymm := isSymm_intMat L
  have h3 := alphaP_blk_odd hvO heO ha hO2 hEsym hEe (fun h => hEd (h ▸ dvd_zero _))
  have hU := alphaP_blk_two_rho hv he hBs hB
  -- renaming the variables
  have r1 : Reidx (blk 2 (intMat (DyBlock.sq 0 u :: L)) B) (blk 1 O (blk 2 E B)) := by
    rw [blk_eq_orthSum, blk_eq_orthSum 1, one_smul_int, blk_eq_orthSum]
    exact (reidx_orthSum_left _ (reidx_append [DyBlock.sq 0 u] L)).trans (reidx_orthSum_assoc _ _ _).symm
  have r2 : Reidx (intMat (DyBlock.sq 0 u :: L)) (blk 1 O E) := by
    rw [blk_eq_orthSum 1, one_smul_int]
    exact reidx_append [DyBlock.sq 0 u] L
  rw [alphaP_reidx r1, h1, h2] at hU
  rw [alphaP_reidx r2, h3] at hU
  have hr : rhoO O (blk 2 E B) = rhoO O E * pB B := rhoO_blk' rfl hOd hEs hEe hEd hBs.eq
  rw [hr] at hU
  have hpos1 := rhoO_pos (O := O) (M := E)
  have hpos2 := alphaP_pos Nat.prime_two (isSymm_intMat [DyBlock.sq 0 u]) (det_intMat_ne _ hvO)
  have hpos3 := alphaP_pos Nat.prime_two hEsym (fun h => hEd (h ▸ dvd_zero _))
  have hpos4 := alphaP_pos Nat.prime_two (smul_isSymm (p := 2) hBs) (smul_det_ne (p := 2) hB)
  have hne : rhoO O E * alphaP 2 O * alphaP 2 E * alphaP 2 (((2 : ℕ) : ℤ) • B) ≠ 0 := by positivity
  apply mul_right_cancel₀ hne
  linear_combination hU.symm

end QuadFormsKB.ConwaySloane.Mass.Two
