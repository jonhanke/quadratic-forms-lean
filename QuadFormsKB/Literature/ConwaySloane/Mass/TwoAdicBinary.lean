/-
# The proportion $\rho$ when the unimodular constituent is odd of dimension two

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), §12, p. 281 (bibliography key `conwaysloane1988`).

For $O = \langle u, v\rangle$ ($u, v$ odd) and $E$ even unimodular, the condition `GoodO` on a $(e \times 2)$ integer matrix
$W$ is explicit. First (`zpEquiv_binary_iff`): for a symmetric integral $2 \times 2$ matrix $S$ with odd diagonal and
even off-diagonal entry, $S$ is equivalent to $\langle u, v\rangle$ over $\mathbb Z_2$ iff $\det S \equiv uv \pmod 8$ and
(when $u \equiv v \pmod 4$) $S_{00} \equiv u \pmod 4$. Then (`goodO_binary_E_iff`): $W$ is good iff its two columns are
congruent modulo $2$ and ($u + v \equiv 0 \pmod 4$ or $w_0^{\mathsf T}Ew_0 \equiv 0 \pmod 4$). Finally
(`rhoO_binary_E`) the proportion $\rho_O(E)$ is $2^{-e}$ times $1$ or the proportion of columns $x$ modulo $8$ with
$x^{\mathsf T}Ex \equiv 0 \pmod 4$. Indices are 0-based.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicRhoOdd

set_option linter.unusedSectionVars false

namespace QuadFormsKB.ConwaySloane.Mass.Two

open Matrix QuadFormsKB.Cassels QuadFormsKB.ConwaySloane

/-! ### Divisibility by $8$ and $4$ through $\mathbb Z/8$ -/

theorem z8_dvd_iff (z : ℤ) : (8 : ℤ) ∣ z ↔ (z : ZMod (2 ^ 3)) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; norm_num

theorem z8_dvd_of_eq {x y : ℤ} (h : (x : ZMod (2 ^ 3)) = y) : (8 : ℤ) ∣ x - y := by
  rw [z8_dvd_iff]; push_cast; rw [h, sub_self]

theorem z4_dvd_iff (z : ℤ) : (4 : ℤ) ∣ z ↔ (z : ZMod (2 ^ 3)) = 0 ∨ (z : ZMod (2 ^ 3)) = 4 := by
  have h4 : ((z - 4 : ℤ) : ZMod (2 ^ 3)) = 0 ↔ (z : ZMod (2 ^ 3)) = 4 := by
    push_cast; exact sub_eq_zero
  rw [← h4, ← z8_dvd_iff, ← z8_dvd_iff]
  omega

theorem z_odd_cases {z : ℤ} (h : ¬ 2 ∣ z) :
    (z : ZMod (2 ^ 3)) = 1 ∨ (z : ZMod (2 ^ 3)) = 3 ∨ (z : ZMod (2 ^ 3)) = 5 ∨ (z : ZMod (2 ^ 3)) = 7 := by
  have key : ∀ k : ℤ, (8 : ℤ) ∣ z - k → (z : ZMod (2 ^ 3)) = (k : ZMod (2 ^ 3)) := fun k hk => by
    have := (z8_dvd_iff _).mp hk
    push_cast at this
    exact sub_eq_zero.mp this
  have : (8 : ℤ) ∣ z - 1 ∨ (8 : ℤ) ∣ z - 3 ∨ (8 : ℤ) ∣ z - 5 ∨ (8 : ℤ) ∣ z - 7 := by omega
  rcases this with h | h | h | h
  · left; simpa using key 1 h
  · right; left; simpa using key 3 h
  · right; right; left; simpa using key 5 h
  · right; right; right; simpa using key 7 h

theorem z_even_cases {z : ℤ} (h : 2 ∣ z) :
    (z : ZMod (2 ^ 3)) = 0 ∨ (z : ZMod (2 ^ 3)) = 2 ∨ (z : ZMod (2 ^ 3)) = 4 ∨ (z : ZMod (2 ^ 3)) = 6 := by
  have key : ∀ k : ℤ, (8 : ℤ) ∣ z - k → (z : ZMod (2 ^ 3)) = (k : ZMod (2 ^ 3)) := fun k hk => by
    have := (z8_dvd_iff _).mp hk
    push_cast at this
    exact sub_eq_zero.mp this
  have : (8 : ℤ) ∣ z - 0 ∨ (8 : ℤ) ∣ z - 2 ∨ (8 : ℤ) ∣ z - 4 ∨ (8 : ℤ) ∣ z - 6 := by omega
  rcases this with h | h | h | h
  · left; simpa using key 0 h
  · right; left; simpa using key 2 h
  · right; right; left; simpa using key 4 h
  · right; right; right; simpa using key 6 h

theorem quad_entry (T : Matrix (Fin 2) (Fin 2) ℤ) (u v : ℤ) (i j : Fin 2) :
    (Tᵀ * !![u, 0; 0, v] * T) i j = u * T 0 i * T 0 j + v * T 1 i * T 1 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-! ### Finite checks over $\mathbb Z/8$ -/

set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem fact_fwd : ∀ u v x y : ZMod (2 ^ 3), (u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7) → (v = 1 ∨ v = 3 ∨ v = 5 ∨ v = 7) →
    (u - v = 0 ∨ u - v = 4) →
    (u * x * x + v * y * y = 1 ∨ u * x * x + v * y * y = 3 ∨ u * x * x + v * y * y = 5 ∨
      u * x * x + v * y * y = 7) →
    ((u * x * x + v * y * y) - u = 0 ∨ (u * x * x + v * y * y) - u = 4) := by
  decide +kernel

/-- The entries of $T^{\mathsf T}\operatorname{diag}(u, v)T$ for $T = H\begin{pmatrix}1 & ab\\ 0 & 1\end{pmatrix}$,
$H = (h_{ij})$, are $a, b, c$ (over $\mathbb Z/8$). -/
abbrev okT (u v a b c h00 h01 h10 h11 : ZMod (2 ^ 3)) : Prop :=
  u * h00 * h00 + v * h10 * h10 = a ∧
  u * h00 * (h00 * (a * b) + h01) + v * h10 * (h10 * (a * b) + h11) = b ∧
  u * (h00 * (a * b) + h01) * (h00 * (a * b) + h01) + v * (h10 * (a * b) + h11) * (h10 * (a * b) + h11) = c

instance (u v a b c h00 h01 h10 h11 : ZMod (2 ^ 3)) : Decidable (okT u v a b c h00 h01 h10 h11) := by
  unfold okT; infer_instance

set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem fact_bwd : ∀ u v a b c : ZMod (2 ^ 3), (u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7) → (v = 1 ∨ v = 3 ∨ v = 5 ∨ v = 7) →
    (a = 1 ∨ a = 3 ∨ a = 5 ∨ a = 7) → (c = 1 ∨ c = 3 ∨ c = 5 ∨ c = 7) →
    (b = 0 ∨ b = 2 ∨ b = 4 ∨ b = 6) →
    a * c - b * b = u * v → (u - v = 0 ∨ u - v = 4 → a - u = 0 ∨ a - u = 4) →
    okT u v a b c 1 0 0 1 ∨ okT u v a b c 0 1 1 0 ∨ okT u v a b c 1 (-2 * u * v) 2 1 ∨
      okT u v a b c (-2 * u * v) 1 1 2 := by
  decide +kernel

/-! ### Equivalence to a diagonal binary form -/

/-- A congruence modulo $8$ by $T = H\begin{pmatrix}1 & ab\\ 0 & 1\end{pmatrix}$ with $\det H$ odd gives a
$\mathbb Z_2$-equivalence. -/
theorem equiv_of_okT {u v : ℤ} (hu : ¬ 2 ∣ u) (hv : ¬ 2 ∣ v) {S : Matrix (Fin 2) (Fin 2) ℤ} (hSs : Sᵀ = S)
    (h00 h01 h10 h11 : ℤ) (hdet : Odd (h00 * h11 - h01 * h10))
    (hok : okT (u : ZMod (2 ^ 3)) v (S 0 0) (S 0 1) (S 1 1) h00 h01 h10 h11) :
    ZpEquiv ((!![u, 0; 0, v] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ_[2]))
      (S.map (Int.cast : ℤ → ℚ_[2])) := by
  set O : Matrix (Fin 2) (Fin 2) ℤ := !![u, 0; 0, v] with hO
  set T0 : Matrix (Fin 2) (Fin 2) ℤ :=
    !![h00, h00 * (S 0 0 * S 0 1) + h01; h10, h10 * (S 0 0 * S 0 1) + h11] with hT0
  have hOs : Oᵀ = O := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hO]
  have hOd : Odd O.det := by
    rw [hO, Matrix.det_fin_two_of]
    simp only [mul_zero, sub_zero]
    exact Odd.mul (Int.not_even_iff_odd.mp fun h => hu (even_iff_two_dvd.mp h))
      (Int.not_even_iff_odd.mp fun h => hv (even_iff_two_dvd.mp h))
  have hTd : Odd T0.det := by
    rw [hT0, Matrix.det_fin_two_of]
    convert hdet using 1; ring
  have t00 : T0 0 0 = h00 := by simp [hT0]
  have t01 : T0 0 1 = h00 * (S 0 0 * S 0 1) + h01 := by simp [hT0]
  have t10 : T0 1 0 = h10 := by simp [hT0]
  have t11 : T0 1 1 = h10 * (S 0 0 * S 0 1) + h11 := by simp [hT0]
  have hSsymm : S 1 0 = S 0 1 := congrFun (congrFun hSs 0) 1
  obtain ⟨e1, e2, e3⟩ := hok
  have key : ∀ x y : ℤ, (x : ZMod (2 ^ 3)) = y → (8 : ℤ) ∣ x - y := fun x y h => z8_dvd_of_eq h
  refine dyadic_zpEquiv_of_int O S T0 hOs hSs hOd hTd ?_
  rw [Fin.forall_fin_two]
  refine ⟨?_, ?_⟩ <;> rw [Fin.forall_fin_two] <;> refine ⟨?_, ?_⟩ <;> rw [hO, quad_entry] <;> apply key <;>
    simp only [t00, t01, t10, t11, hSsymm] <;> push_cast
  · exact e1
  · linear_combination e2
  · linear_combination e2
  · exact e3

/-- **Equivalence of an odd binary form with even cross term to $\langle u, v\rangle$ over $\mathbb Z_2$.** Let
$u, v$ be odd and $S$ a symmetric integral $2 \times 2$ matrix with $S_{00}$, $S_{11}$ odd and $S_{01}$ even. Then
$S$ is $\mathbb Z_2$-equivalent to $\operatorname{diag}(u, v)$ iff $\det S \equiv uv \pmod 8$ and, when
$u \equiv v \pmod 4$, also $S_{00} \equiv u \pmod 4$. -/
@[kb "conwaysloane1988" "§12, p. 281 (p = 2, binary odd part)"]
theorem zpEquiv_binary_iff {u v : ℤ} (hu : ¬ 2 ∣ u) (hv : ¬ 2 ∣ v) {S : Matrix (Fin 2) (Fin 2) ℤ} (hSs : Sᵀ = S)
    (ha : ¬ 2 ∣ S 0 0) (hc : ¬ 2 ∣ S 1 1) (hb : 2 ∣ S 0 1) :
    ZpEquiv ((!![u, 0; 0, v] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ_[2]))
      (S.map (Int.cast : ℤ → ℚ_[2])) ↔
      (8 : ℤ) ∣ S.det - u * v ∧ ((4 : ℤ) ∣ u - v → (4 : ℤ) ∣ S 0 0 - u) := by
  have hSsymm : S 1 0 = S 0 1 := congrFun (congrFun hSs 0) 1
  have hdetS : S.det = S 0 0 * S 1 1 - S 0 1 * S 0 1 := by
    rw [Matrix.det_fin_two, hSsymm]
  constructor
  · intro h
    obtain ⟨G, hG, hGe⟩ := exists_unit_congr_of_zpEquiv (p := 2) h 3
    have e00 := congrFun (congrFun hGe 0) 0
    have e01 := congrFun (congrFun hGe 0) 1
    have e11 := congrFun (congrFun hGe 1) 1
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, Matrix.map_apply,
      Matrix.of_apply, Int.coe_castRingHom] at e00 e01 e11
    simp at e00 e01 e11
    have hd : IsUnit (G 0 0 * G 1 1 - G 0 1 * G 1 0) := by
      have := (Matrix.isUnit_iff_isUnit_det G).mp hG
      rwa [Matrix.det_fin_two] at this
    have hsq := zmod8_unit_sq hd
    constructor
    · rw [z8_dvd_iff, hdetS]
      push_cast
      rw [← e00, ← e01, ← e11]
      linear_combination ((u : ZMod (2 ^ 3)) * v) * hsq
    · intro h4
      rw [z4_dvd_iff] at h4 ⊢
      push_cast at h4 ⊢
      have e00' : (S 0 0 : ZMod (2 ^ 3)) = u * G 0 0 * G 0 0 + v * G 1 0 * G 1 0 := by
        rw [← e00]; ring
      have hodd := z_odd_cases ha
      rw [e00'] at hodd ⊢
      exact fact_fwd _ _ _ _ (z_odd_cases hu) (z_odd_cases hv) h4 hodd
  · rintro ⟨h8, h4⟩
    have hdet : (S 0 0 : ZMod (2 ^ 3)) * S 1 1 - S 0 1 * S 0 1 = u * v := by
      have := (z8_dvd_iff _).mp h8
      rw [hdetS] at this
      push_cast at this
      exact sub_eq_zero.mp this
    have h4' : ((u : ZMod (2 ^ 3)) - v = 0 ∨ (u : ZMod (2 ^ 3)) - v = 4) →
        ((S 0 0 : ZMod (2 ^ 3)) - u = 0 ∨ (S 0 0 : ZMod (2 ^ 3)) - u = 4) := by
      intro h
      have := (z4_dvd_iff _).mp (h4 ((z4_dvd_iff _).mpr (by push_cast; exact h)))
      push_cast at this
      exact this
    rcases fact_bwd _ _ _ _ _ (z_odd_cases hu) (z_odd_cases hv) (z_odd_cases ha) (z_odd_cases hc)
      (z_even_cases hb) hdet h4' with h | h | h | h
    · exact equiv_of_okT hu hv hSs 1 0 0 1 ⟨0, by norm_num⟩ (by push_cast; exact h)
    · exact equiv_of_okT hu hv hSs 0 1 1 0 ⟨-1, by norm_num⟩ (by push_cast; exact h)
    · exact equiv_of_okT hu hv hSs 1 (-2 * u * v) 2 1 ⟨2 * u * v, by ring⟩ (by push_cast; exact h)
    · exact equiv_of_okT hu hv hSs (-2 * u * v) 1 1 2 ⟨-2 * u * v - 1, by ring⟩ (by push_cast; exact h)

/-! ### The condition `GoodO` for $O = \langle u, v\rangle$ and $E$ even unimodular -/

set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem fact_key : ∀ u v q s m : ZMod (2 ^ 3), (u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7) → (v = 1 ∨ v = 3 ∨ v = 5 ∨ v = 7) →
    (q = 0 ∨ q = 2 ∨ q = 4 ∨ q = 6) →
    (((u + q) * (v + (q + 4 * s + 8 * m)) - (q + 2 * s) * (q + 2 * s) - u * v = 0 ∧
      ((u - v = 0 ∨ u - v = 4) → ((u + q) - u = 0 ∨ (u + q) - u = 4))) ↔
      ((u + v = 0 ∨ u + v = 4) ∨ (q = 0 ∨ q = 4))) := by
  decide +kernel

/-- The arithmetic of the determinant and the diagonal of $\operatorname{diag}(u, v) + Q$, with
$Q = (q, q + 2s; q + 2s, q + 4s + 8m)$. -/
theorem key_arith {u v q s m : ℤ} (hu : ¬ 2 ∣ u) (hv : ¬ 2 ∣ v) (hq : 2 ∣ q) :
    ((8 : ℤ) ∣ (u + q) * (v + (q + 4 * s + 8 * m)) - (q + 2 * s) * (q + 2 * s) - u * v ∧
      ((4 : ℤ) ∣ u - v → (4 : ℤ) ∣ (u + q) - u)) ↔ ((4 : ℤ) ∣ u + v ∨ (4 : ℤ) ∣ q) := by
  rw [z8_dvd_iff, z4_dvd_iff, z4_dvd_iff, z4_dvd_iff, z4_dvd_iff]
  push_cast
  exact fact_key _ _ _ _ _ (z_odd_cases hu) (z_odd_cases hv) (z_even_cases hq)

section Bil

variable {e : ℕ} (E : Matrix (Fin e) (Fin e) ℤ)

/-- The bilinear form $(x, y) \mapsto x^{\mathsf T}Ey$ on vectors $\mathbb Z^e$ (indexed by `Fin e`). -/
def bil (x y : Fin e → ℤ) : ℤ := ∑ k, ∑ l, x k * E k l * y l

theorem bil_comm (hEs : Eᵀ = E) (x y : Fin e → ℤ) : bil E x y = bil E y x := by
  unfold bil
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  have : E l k = E k l := congrFun (congrFun hEs k) l
  rw [this]; ring

theorem bil_add_snd (x y d : Fin e → ℤ) : bil E x (fun l => y l + 2 * d l) = bil E x y + 2 * bil E x d := by
  unfold bil
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem bil_add_fst (hEs : Eᵀ = E) (y d z : Fin e → ℤ) :
    bil E (fun l => y l + 2 * d l) z = bil E y z + 2 * bil E d z := by
  rw [bil_comm E hEs _ z, bil_add_snd, bil_comm E hEs z y, bil_comm E hEs z d]

theorem bil_even (hEs : Eᵀ = E) (hEe : EvenDiag E) (x : Fin e → ℤ) : ∃ m, bil E x x = 2 * m := by
  have h := diag_quad hEs hEe (Matrix.of fun k (_ : Fin 1) => x k) 0
  refine ⟨((Matrix.of fun k (_ : Fin 1) => x k)ᵀ * halfUp E * Matrix.of fun k (_ : Fin 1) => x k) 0 0, ?_⟩
  rw [← h]
  simp only [bil, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem quad_apply (W : Matrix (Fin e) (Fin 2) ℤ) (i j : Fin 2) :
    (Wᵀ * E * W) i j = bil E (fun k => W k i) (fun k => W k j) := by
  simp only [bil, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

end Bil

theorem par_iff {u v : ℤ} (hu : ¬ 2 ∣ u) (hv : ¬ 2 ∣ v) (x y : ℤ) : 2 ∣ v * x * x + u * y * y ↔ 2 ∣ x + y := by
  have hu' : ¬ Even u := fun h => hu (even_iff_two_dvd.mp h)
  have hv' : ¬ Even v := fun h => hv (even_iff_two_dvd.mp h)
  simp only [← even_iff_two_dvd, Int.even_add, Int.even_mul, hu', hv', false_or]
  tauto

/-- **The second condition of `GoodO` for $O = \langle u, v\rangle$**: the perturbed block has even diagonal iff the
two columns of $W$ are congruent modulo $2$ ($E$ even unimodular). -/
theorem evenDiag_binary_iff {e : ℕ} {E : Matrix (Fin e) (Fin e) ℤ} (hEs : Eᵀ = E) (hEd : ¬ 2 ∣ E.det) {u v : ℤ}
    (hu : ¬ 2 ∣ u) (hv : ¬ 2 ∣ v) (W : Matrix (Fin e) (Fin 2) ℤ) :
    EvenDiag (E * W * (!![u, 0; 0, v] : Matrix (Fin 2) (Fin 2) ℤ).adjugate * Wᵀ * E) ↔
      ∀ k, 2 ∣ W k 0 - W k 1 := by
  set P := E * W with hPdef
  have hP : E * W * (!![u, 0; 0, v] : Matrix (Fin 2) (Fin 2) ℤ).adjugate * Wᵀ * E =
      P * (!![u, 0; 0, v] : Matrix (Fin 2) (Fin 2) ℤ).adjugate * Pᵀ := by
    rw [hPdef, Matrix.transpose_mul, hEs]; simp only [Matrix.mul_assoc]
  have hd : ∀ i, (P * (!![u, 0; 0, v] : Matrix (Fin 2) (Fin 2) ℤ).adjugate * Pᵀ) i i =
      v * P i 0 * P i 0 + u * P i 1 * P i 1 := by
    intro i
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two_of]
    ring
  let Z : Matrix (Fin e) (Fin 1) ℤ := Matrix.of fun k _ => W k 0 + W k 1
  have hZ : ∀ i, (E * Z) i 0 = P i 0 + P i 1 := by
    intro i
    simp only [Z, hPdef, Matrix.mul_apply, Matrix.of_apply, mul_add, Finset.sum_add_distrib]
  unfold EvenDiag
  rw [hP]
  simp only [hd, par_iff hu hv]
  constructor
  · intro h k
    have := two_dvd_of_mul_unimod hEd (Y := Z) fun i => by rw [hZ]; exact h i
    have h2 := this k
    simp only [Z, Matrix.of_apply] at h2
    omega
  · intro h i
    rw [← hZ]
    rw [Matrix.mul_apply]
    exact Finset.dvd_sum fun j _ => by
      have := h j
      simp only [Z, Matrix.of_apply]
      exact Dvd.dvd.mul_left (by omega) _

/-- When the two columns of $W$ are congruent modulo $2$, the first condition of `GoodO` is
$u + v \equiv 0 \pmod 4$ or $w_0^{\mathsf T}Ew_0 \equiv 0 \pmod 4$. -/
theorem goodO1_binary_iff {e : ℕ} {E : Matrix (Fin e) (Fin e) ℤ} (hEs : Eᵀ = E) (hEe : EvenDiag E) {u v : ℤ}
    (hu : ¬ 2 ∣ u) (hv : ¬ 2 ∣ v) (W : Matrix (Fin e) (Fin 2) ℤ) (hp : ∀ k, 2 ∣ W k 0 - W k 1) :
    GoodO1 (!![u, 0; 0, v] : Matrix (Fin 2) (Fin 2) ℤ) E W ↔ ((4 : ℤ) ∣ u + v ∨ (4 : ℤ) ∣ (Wᵀ * E * W) 0 0) := by
  choose c hc using hp
  set w0 : Fin e → ℤ := fun k => W k 0 with hw0
  set d : Fin e → ℤ := fun k => -c k with hd
  have hw1 : (fun k => W k 1) = fun l => w0 l + 2 * d l := by
    funext k; simp only [hw0, hd]; linarith [hc k]
  obtain ⟨m, hm⟩ := bil_even E hEs hEe d
  obtain ⟨q', hq'⟩ := bil_even E hEs hEe w0
  set q := bil E w0 w0 with hq
  set s := bil E w0 d with hs
  have hdw : bil E d w0 = s := bil_comm E hEs _ _
  have hQ00 : (Wᵀ * E * W) 0 0 = q := by rw [quad_apply]
  have hQ01 : (Wᵀ * E * W) 0 1 = q + 2 * s := by
    rw [quad_apply, hw1, bil_add_snd]
  have hQ10 : (Wᵀ * E * W) 1 0 = q + 2 * s := by
    rw [← hQ01]; exact congrFun (congrFun (quad_symm hEs W) 0) 1
  have hQ11 : (Wᵀ * E * W) 1 1 = q + 4 * s + 8 * m := by
    rw [quad_apply, hw1, bil_add_fst E hEs, bil_add_snd, bil_add_snd, hdw, hm]
    ring
  have hqe : 2 ∣ q := ⟨q', hq'⟩
  have hS00 : ((!![u, 0; 0, v] : Matrix (Fin 2) (Fin 2) ℤ) + Wᵀ * E * W) 0 0 = u + q := by
    simp [hQ00]
  have hS01 : ((!![u, 0; 0, v] : Matrix (Fin 2) (Fin 2) ℤ) + Wᵀ * E * W) 0 1 = q + 2 * s := by
    simp [hQ01]
  have hS10 : ((!![u, 0; 0, v] : Matrix (Fin 2) (Fin 2) ℤ) + Wᵀ * E * W) 1 0 = q + 2 * s := by
    simp [hQ10]
  have hS11 : ((!![u, 0; 0, v] : Matrix (Fin 2) (Fin 2) ℤ) + Wᵀ * E * W) 1 1 = v + (q + 4 * s + 8 * m) := by
    simp [hQ11]
  have hSs : ((!![u, 0; 0, v] : Matrix (Fin 2) (Fin 2) ℤ) + Wᵀ * E * W)ᵀ =
      (!![u, 0; 0, v] : Matrix (Fin 2) (Fin 2) ℤ) + Wᵀ * E * W := by
    rw [transpose_add, quad_symm hEs]
    congr 1
    ext i j; fin_cases i <;> fin_cases j <;> simp
  unfold GoodO1
  rw [zpEquiv_binary_iff hu hv hSs (by rw [hS00]; omega) (by rw [hS11]; omega) (by rw [hS01]; omega),
    Matrix.det_fin_two, hS10, hS00, hS01, hS11, hQ00]
  exact key_arith hu hv hqe

/-- **The condition `GoodO` for $O = \langle u, v\rangle$ and $E$ even unimodular**, $u, v$ odd: the columns $w_0, w_1$
of $W$ satisfy $w_0 \equiv w_1 \pmod 2$, and $u + v \equiv 0 \pmod 4$ or $w_0^{\mathsf T}Ew_0 \equiv 0 \pmod 4$. -/
@[kb "conwaysloane1988" "§12, p. 281 (p = 2, binary odd part)"]
theorem goodO_binary_E_iff {e : ℕ} {E : Matrix (Fin e) (Fin e) ℤ} (hEs : Eᵀ = E) (hEe : EvenDiag E)
    (hEd : ¬ 2 ∣ E.det) {u v : ℤ} (hu : ¬ 2 ∣ u) (hv : ¬ 2 ∣ v) (W : Matrix (Fin e) (Fin 2) ℤ) :
    GoodO (!![u, 0; 0, v] : Matrix (Fin 2) (Fin 2) ℤ) E W ↔
      (∀ k, 2 ∣ W k 0 - W k 1) ∧ ((4 : ℤ) ∣ u + v ∨ (4 : ℤ) ∣ (Wᵀ * E * W) 0 0) := by
  unfold GoodO
  constructor
  · rintro ⟨h1, h2⟩
    have hp := (evenDiag_binary_iff hEs hEd hu hv W).mp h2
    exact ⟨hp, (goodO1_binary_iff hEs hEe hu hv W hp).mp h1⟩
  · rintro ⟨hp, h⟩
    exact ⟨(goodO1_binary_iff hEs hEe hu hv W hp).mpr h, (evenDiag_binary_iff hEs hEd hu hv W).mpr hp⟩

/-! ### Counting modulo $8$ -/

/-- The columns of an $e \times 2$ matrix. -/
def colsEquiv (e : ℕ) (α : Type*) : Matrix (Fin e) (Fin 2) α ≃ (Fin e → α) × (Fin e → α) where
  toFun W := (fun k => W k 0, fun k => W k 1)
  invFun p := Matrix.of fun k => ![p.1 k, p.2 k]
  left_inv W := by ext k j; fin_cases j <;> rfl
  right_inv p := rfl

/-- A column of an $e \times 1$ matrix. -/
def colEquiv (e : ℕ) (α : Type*) : Matrix (Fin e) (Fin 1) α ≃ (Fin e → α) where
  toFun W := fun k => W k 0
  invFun x := Matrix.of fun k _ => x k
  left_inv W := by ext k j; rw [Subsingleton.elim j 0]; rfl
  right_inv x := rfl

/-- The vectors $y$ modulo $8$ congruent to a given vector modulo $2$ number $4^e$. -/
theorem card_par (e : ℕ) (x : Fin e → ZMod (2 ^ 3)) :
    Nat.card {y : Fin e → ZMod (2 ^ 3) // ∀ k, (2 : ℤ) ∣ ((x k).val : ℤ) - ((y k).val : ℤ)} = 4 ^ e := by
  have hc := Nat.card_congr (Equiv.subtypePiEquivPi (β := fun _ : Fin e => ZMod (2 ^ 3))
    (p := fun k t => (2 : ℤ) ∣ ((x k).val : ℤ) - (t.val : ℤ)))
  have h4 : ∀ a : ZMod (2 ^ 3),
      Nat.card {t : ZMod (2 ^ 3) // (2 : ℤ) ∣ ((a.val : ℤ) - (t.val : ℤ))} = 4 := by
    intro a
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    revert a
    decide
  rw [hc, Nat.card_pi, Finset.prod_congr rfl fun k _ => h4 (x k)]
  simp

theorem quad1_apply {e : ℕ} (E : Matrix (Fin e) (Fin e) ℤ) (Y : Matrix (Fin e) (Fin 1) ℤ) :
    (Yᵀ * E * Y) 0 0 = bil E (fun k => Y k 0) (fun k => Y k 0) := by
  simp only [bil, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- **The number of good $W$ modulo $8$**: $\#\{x : u + v \equiv 0 \pmod 4 \text{ or } x^{\mathsf T}Ex \equiv 0
\pmod 4\}\cdot 4^e$ (the second column is any vector congruent to the first modulo $2$). -/
theorem card_goodO_binary {e : ℕ} {E : Matrix (Fin e) (Fin e) ℤ} (hEs : Eᵀ = E) (hEe : EvenDiag E)
    (hEd : ¬ 2 ∣ E.det) {u v : ℤ} (hu : ¬ 2 ∣ u) (hv : ¬ 2 ∣ v) :
    Nat.card {W : Matrix (Fin e) (Fin 2) (ZMod (2 ^ 3)) //
        GoodO (!![u, 0; 0, v] : Matrix (Fin 2) (Fin 2) ℤ) E (lift W)} =
      Nat.card {x : Fin e → ZMod (2 ^ 3) // (4 : ℤ) ∣ u + v ∨
        (4 : ℤ) ∣ bil E (fun k => ((x k).val : ℤ)) (fun k => ((x k).val : ℤ))} * 4 ^ e := by
  set P : (Fin e → ZMod (2 ^ 3)) → Prop := fun x => (4 : ℤ) ∣ u + v ∨
    (4 : ℤ) ∣ bil E (fun k => ((x k).val : ℤ)) (fun k => ((x k).val : ℤ)) with hP
  have h1 : Nat.card {W : Matrix (Fin e) (Fin 2) (ZMod (2 ^ 3)) //
        GoodO (!![u, 0; 0, v] : Matrix (Fin 2) (Fin 2) ℤ) E (lift W)} =
      Nat.card {p : (Fin e → ZMod (2 ^ 3)) × (Fin e → ZMod (2 ^ 3)) //
        (∀ k, (2 : ℤ) ∣ ((p.1 k).val : ℤ) - ((p.2 k).val : ℤ)) ∧ P p.1} :=
    Nat.card_congr ((colsEquiv e _).subtypeEquiv fun W => by
      rw [goodO_binary_E_iff hEs hEe hEd hu hv, quad_apply]
      exact Iff.rfl)
  have h2 : Nat.card {p : (Fin e → ZMod (2 ^ 3)) × (Fin e → ZMod (2 ^ 3)) //
        (∀ k, (2 : ℤ) ∣ ((p.1 k).val : ℤ) - ((p.2 k).val : ℤ)) ∧ P p.1} =
      Nat.card (Σ x : {x : Fin e → ZMod (2 ^ 3) // P x},
        {y : Fin e → ZMod (2 ^ 3) // ∀ k, (2 : ℤ) ∣ ((x.1 k).val : ℤ) - ((y k).val : ℤ)}) :=
    Nat.card_congr
      { toFun := fun p => ⟨⟨p.1.1, p.2.2⟩, ⟨p.1.2, p.2.1⟩⟩
        invFun := fun s => ⟨(s.1.1, s.2.1), s.2.2, s.1.2⟩
        left_inv := fun p => rfl
        right_inv := fun s => rfl }
  rw [h1, h2, Nat.card_sigma, Finset.sum_congr rfl fun x _ => card_par e x.1]
  simp [Nat.card_eq_fintype_card]

/-- **The proportion $\rho_O(E)$ for $O = \langle u, v\rangle$ and $E$ even unimodular**: $2^{-e}$ times $1$ if
$u + v \equiv 0 \pmod 4$, and otherwise the proportion of $x \in (\mathbb Z/8)^e$ with $x^{\mathsf T}Ex \equiv 0
\pmod 4$. -/
@[kb "conwaysloane1988" "§12, p. 281 (p = 2, binary odd part)"]
theorem rhoO_binary_E {e : ℕ} {E : Matrix (Fin e) (Fin e) ℤ} (hEs : Eᵀ = E) (hEe : EvenDiag E)
    (hEd : ¬ 2 ∣ E.det) {u v : ℤ} (hu : ¬ 2 ∣ u) (hv : ¬ 2 ∣ v) :
    rhoO (!![u, 0; 0, v] : Matrix (Fin 2) (Fin 2) ℤ) E =
      (1 / 2 : ℝ) ^ e * (if (4 : ℤ) ∣ u + v then 1 else
        (Nat.card {x : Matrix (Fin e) (Fin 1) (ZMod (2 ^ 3)) //
          (4 : ℤ) ∣ ((lift x)ᵀ * E * lift x) 0 0} : ℝ) / 8 ^ e) := by
  unfold rhoO
  rw [card_goodO_binary hEs hEe hEd hu hv]
  have h8 : (8 : ℝ) ^ e = 2 ^ e * 4 ^ e := by rw [← mul_pow]; norm_num
  have hX : Nat.card (Fin e → ZMod (2 ^ 3)) = 8 ^ e := by
    rw [Nat.card_eq_fintype_card]; simp [ZMod.card]
  by_cases h4 : (4 : ℤ) ∣ u + v
  · have hN : Nat.card {x : Fin e → ZMod (2 ^ 3) // (4 : ℤ) ∣ u + v ∨
        (4 : ℤ) ∣ bil E (fun k => ((x k).val : ℤ)) (fun k => ((x k).val : ℤ))} = 8 ^ e := by
      rw [← hX]; exact Nat.card_congr (Equiv.subtypeUnivEquiv fun x => Or.inl h4)
    rw [hN]
    simp only [h4, ↓reduceIte]
    push_cast
    rw [mul_one, pow_mul, h8, one_div, inv_pow]
    field_simp
  · have hN : Nat.card {x : Fin e → ZMod (2 ^ 3) // (4 : ℤ) ∣ u + v ∨
        (4 : ℤ) ∣ bil E (fun k => ((x k).val : ℤ)) (fun k => ((x k).val : ℤ))} =
        Nat.card {x : Matrix (Fin e) (Fin 1) (ZMod (2 ^ 3)) // (4 : ℤ) ∣ ((lift x)ᵀ * E * lift x) 0 0} :=
      (Nat.card_congr ((colEquiv e (ZMod (2 ^ 3))).subtypeEquiv fun x => by
        rw [quad1_apply]
        simp only [h4, false_or]
        exact Iff.rfl)).symm
    rw [hN]
    simp only [h4, ↓reduceIte]
    push_cast
    rw [pow_mul, h8, one_div, inv_pow]
    field_simp

/-! ### The model matrix `intMat [sq 0 u, sq 0 v]` -/

/-- The Gram matrix of the model $\langle u, v\rangle$ of two blocks $u x^2$ of exponent $0$ is
$\operatorname{diag}(u, v)$. -/
theorem intMat_sq_sq (u v : ℤ) :
    (intMat [DyBlock.sq 0 u, DyBlock.sq 0 v] : Matrix (Fin 2) (Fin 2) ℤ) = !![u, 0; 0, v] := by
  ext i j
  fin_cases i <;> fin_cases j
  · show (2 : ℤ) ^ (0 : ℤ).toNat * u = u
    simp
  · show (0 : ℤ) = 0
    rfl
  · show (0 : ℤ) = 0
    rfl
  · show (2 : ℤ) ^ (0 : ℤ).toNat * v = v
    simp

/-- **$\rho_O(E)$ for the model $O$ = `intMat [sq 0 u, sq 0 v]`** (two blocks $u x^2$, $v x^2$ of exponent $0$,
$u, v$ odd): $2^{-e}$ times $1$ if $u + v \equiv 0 \pmod 4$, and otherwise the proportion of $x \in (\mathbb
Z/8)^e$ with $x^{\mathsf T}Ex \equiv 0 \pmod 4$. -/
@[kb "conwaysloane1988" "§12, p. 281 (p = 2, binary odd part)"]
theorem rhoO_binary_E_intMat {e : ℕ} {E : Matrix (Fin e) (Fin e) ℤ} (hEs : Eᵀ = E) (hEe : EvenDiag E)
    (hEd : ¬ 2 ∣ E.det) {u v : ℤ} (hu : ¬ 2 ∣ u) (hv : ¬ 2 ∣ v) :
    rhoO (intMat [DyBlock.sq 0 u, DyBlock.sq 0 v]) E =
      (1 / 2 : ℝ) ^ e * (if (4 : ℤ) ∣ u + v then 1 else
        (Nat.card {x : Matrix (Fin e) (Fin 1) (ZMod (2 ^ 3)) //
          (4 : ℤ) ∣ ((lift x)ᵀ * E * lift x) 0 0} : ℝ) / 8 ^ e) :=
  (congrArg (fun O => rhoO O E) (intMat_sq_sq u v)).trans (rhoO_binary_E hEs hEe hEd hu hv)

end QuadFormsKB.ConwaySloane.Mass.Two
