/-
# The proportion $p_B$

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), (3), p. 263, Table 1, p. 264 (bibliography key `conwaysloane1988`).

$p_B$ (`pB`) is the proportion of $z \in (\mathbb Z/8)^b$ with $4 \mid z^{\mathsf T}Bz$. It enters $\rho(U, B)$ for an
odd unimodular $U$ (`rho_sq_cons`). Here $p_B$ is computed from the 2-adic symbol of $B$ (`pB_intMat`): with $f_2$, $f_4$
the constituents of $B$ of scales $1$, $2$,
$p_B = \frac12$ ($f_2$ type II, $f_4$ type I), $P(f_2)$ ($f_2$, $f_4$ type II), $\frac14$ ($f_2$, $f_4$ type I),
$r(f_2)/4$ ($f_2$ type I, $f_4$ type II).

Method: $z^{\mathsf T}Bz \bmod 4$ is the quadratic form of $B \bmod 4$ at $z \bmod 4$ (`cast_quad_col`); its value counts
`qN` multiply by convolution over orthogonal sums (`qN_orthSum`); the part of exponent $\ge 1$ is $2K$ with
$Q_{2K}(y) = 2\sum_k K_{kk}y_k$ (`two_qv_K`), whose values are balanced on $\{0, 2\}$ when some $K_{kk}$ is odd.
Indices are 0-based.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicUnimod

set_option linter.unusedSectionVars false

namespace QuadFormsKB.ConwaySloane.Mass.Two

open Matrix QuadFormsKB.Cassels QuadFormsKB.ConwaySloane

/-! ### Value counts and convolution -/

/-- The number of $y \in (\mathbb Z/4)^n$ with $Q_V(y) = j$. -/
def qN {n : ℕ} (V : Matrix (Fin n) (Fin n) (ZMod (2 ^ 2))) (j : ZMod (2 ^ 2)) : ℕ :=
  (Finset.univ.filter fun y : Fin n → ZMod (2 ^ 2) => qv V y = j).card

theorem card_filter_add {α β : Type*} [Fintype α] [Fintype β] (f : α → ZMod (2 ^ 2)) (g : β → ZMod (2 ^ 2))
    (j : ZMod (2 ^ 2)) :
    (Finset.univ.filter fun p : α × β => f p.1 + g p.2 = j).card =
      ∑ k, (Finset.univ.filter fun a => f a = k).card * (Finset.univ.filter fun b => g b = j - k).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p : α × β => f p.1) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.card_product]
  congr 1
  ext ⟨a, b⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, by rw [← h1, ← h2]; ring⟩
  · rintro ⟨h1, h2⟩; exact ⟨by rw [h1, h2]; ring, h1⟩

theorem qN_orthSum {m n : ℕ} (F : Matrix (Fin m) (Fin m) (ZMod (2 ^ 2))) (G : Matrix (Fin n) (Fin n) (ZMod (2 ^ 2)))
    (j : ZMod (2 ^ 2)) : qN (orthSumMat F G) j = ∑ k, qN F k * qN G (j - k) := by
  classical
  unfold qN
  rw [← card_filter_add (qv F) (qv G) j]
  set e : (Fin (m + n) → ZMod (2 ^ 2)) ≃ (Fin m → ZMod (2 ^ 2)) × (Fin n → ZMod (2 ^ 2)) :=
    (finSumFinEquiv.arrowCongr (Equiv.refl _)).symm.trans (Equiv.sumArrowEquivProdArrow _ _ _)
  refine Finset.card_bij (fun y _ => e y) (fun y hy => ?_) (fun y _ y' _ h => e.injective h) (fun p hp => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    rw [← hy, qv_orthSum]
    rfl
  · refine ⟨e.symm p, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    rw [qv_orthSum]
    have h1 : (fun i => e.symm p (Fin.castAdd n i)) = p.1 := congrArg Prod.fst (e.apply_symm_apply p)
    have h2 : (fun i => e.symm p (Fin.natAdd m i)) = p.2 := congrArg Prod.snd (e.apply_symm_apply p)
    rw [h1, h2]; exact hp

theorem qN_reidx {m n : ℕ} {M : Matrix (Fin m) (Fin m) ℤ} {N : Matrix (Fin n) (Fin n) ℤ} (h : Reidx M N)
    (j : ZMod (2 ^ 2)) : qN (red 2 M) j = qN (red 2 N) j := by
  obtain ⟨e, rfl⟩ := h
  unfold qN
  refine Finset.card_bij (fun y _ => y ∘ e.symm) (fun y hy => ?_) (fun y _ y' _ h => ?_) (fun y hy => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    rw [← hy]
    unfold qv
    simp only [dotProduct, Matrix.mulVec, Function.comp, Matrix.map_apply, Matrix.submatrix_apply]
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← e.sum_comp]
    simp
  · funext i
    have := congrFun h (e i)
    simpa using this
  · refine ⟨y ∘ e, ?_, by funext i; simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    rw [← hy]
    unfold qv
    simp only [dotProduct, Matrix.mulVec, Function.comp, Matrix.map_apply, Matrix.submatrix_apply]
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← e.sum_comp]

/-! ### Entries of `intMat` -/

theorem intMat_entry : ∀ (L : List DyBlock) (k l : Fin (dyDim L)),
    intMat L k l = 0 ∨ ∃ c ∈ L, ∃ i j : Fin c.dim, intMat L k l = bInt c i j
  | [], k, _ => k.elim0
  | c :: L, k, l => by
    show orthSumMat (bInt c) (intMat L) k l = 0 ∨ ∃ c' ∈ c :: L, ∃ i j : Fin c'.dim,
      orthSumMat (bInt c) (intMat L) k l = bInt c' i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) l
    · exact Or.inr ⟨c, by simp, i, j, by rw [orthSumMat_cc]⟩
    · left; rw [orthSumMat_cn]
    · left; rw [orthSumMat_nc]
    · rcases intMat_entry L i j with h | ⟨c', hc', i', j', h⟩
      · left; rw [orthSumMat_nn, h]
      · exact Or.inr ⟨c', by simp [hc'], i', j', by rw [orthSumMat_nn, h]⟩

theorem intMat_diag : ∀ (L : List DyBlock) (k : Fin (dyDim L)), ∃ c ∈ L, ∃ i : Fin c.dim, intMat L k k = bInt c i i
  | [], k => k.elim0
  | c :: L, k => by
    show ∃ c' ∈ c :: L, ∃ i : Fin c'.dim, orthSumMat (bInt c) (intMat L) k k = bInt c' i i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · exact ⟨c, by simp, i, by rw [orthSumMat_cc]⟩
    · obtain ⟨c', hc', i', h⟩ := intMat_diag L i
      exact ⟨c', by simp [hc'], i', by rw [orthSumMat_nn, h]⟩

theorem intMat_diag_of_mem : ∀ (L : List DyBlock), ∀ c ∈ L, ∀ i : Fin c.dim, ∃ k, intMat L k k = bInt c i i
  | [], c, hc, _ => absurd hc (by simp)
  | c' :: L, c, hc, i => by
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨Fin.castAdd _ i, by show orthSumMat (bInt c) (intMat L) _ _ = _; rw [orthSumMat_cc]⟩
    · obtain ⟨k, hk⟩ := intMat_diag_of_mem L c hc i
      exact ⟨Fin.natAdd _ k, by show orthSumMat (bInt c') (intMat L) _ _ = _; rw [orthSumMat_nn, hk]⟩

/-! ### Blocks of positive exponent -/

theorem pow_toNat_succ {e : ℤ} (he : 1 ≤ e) : ∃ m, e.toNat = m + 1 := ⟨e.toNat - 1, by omega⟩

theorem bInt_even (c : DyBlock) (he : 1 ≤ blockExp c) (i j : Fin c.dim) : (2 : ℤ) ∣ bInt c i j := by
  obtain ⟨e, he'⟩ := reidx_bInt_lower c he
  rw [he']
  exact ⟨bInt (lowerB c) (e i) (e j), rfl⟩

theorem bInt_sq_apply (e u : ℤ) (i j : Fin (DyBlock.sq e u).dim) : bInt (DyBlock.sq e u) i j = 2 ^ e.toNat * u := by
  have hi : i = ⟨0, Nat.one_pos⟩ := Fin.ext (by have := i.isLt; simp [DyBlock.dim] at this; omega)
  have hj : j = ⟨0, Nat.one_pos⟩ := Fin.ext (by have := j.isLt; simp [DyBlock.dim] at this; omega)
  subst hi hj
  rfl

/-- A block of positive exponent has a diagonal entry $\equiv 2 \pmod 4$ iff it is $2u x^2$. -/
theorem bInt_diag_high {c : DyBlock} (hv : c.Valid) (he : 1 ≤ blockExp c) (i : Fin c.dim) :
    ¬ (4 : ℤ) ∣ bInt c i i ↔ (IsSqBlock c ∧ blockExp c = 1) := by
  obtain ⟨e, he'⟩ := reidx_bInt_lower c he
  have hentry : bInt c i i = 2 * bInt (lowerB c) (e i) (e i) := by rw [he']; rfl
  rw [hentry]
  constructor
  · intro h
    by_contra hn
    have hev := evenDiag_bInt (lowerB c) (by
      rw [blockExp_lowerB]
      rintro ⟨hs, h0⟩
      apply hn
      refine ⟨?_, by omega⟩
      cases c <;> simp_all [lowerB, IsSqBlock]) (by rw [blockExp_lowerB]; omega)
    obtain ⟨t, ht⟩ := hev (e i)
    exact h ⟨t, by rw [ht]; ring⟩
  · rintro ⟨hs, h1⟩
    cases c with
    | sq e' u =>
      simp only [blockExp] at h1
      subst h1
      have hb : bInt (lowerB (DyBlock.sq 1 u)) (e i) (e i) = u := by
        exact (bInt_sq_apply (1 - 1) u (e i) (e i)).trans (by norm_num)
      rw [hb]
      have hu := valid_odd hv
      intro ⟨t, ht⟩
      apply hu
      exact ⟨t, by linarith⟩
    | hyp e' => exact absurd hs id
    | ell e' => exact absurd hs id

/-- The blocks $2u x^2$ of exponent $1$ (type I of the constituent of scale $2$). -/
def HasSq1 (R : List DyBlock) : Prop := ∃ c ∈ R, IsSqBlock c ∧ blockExp c = 1

theorem qN_high {R : List DyBlock} (hv : ∀ c ∈ R, c.Valid) (he : ∀ c ∈ R, 1 ≤ blockExp c) :
    (∀ j : ZMod (2 ^ 2), j ≠ 0 → j ≠ 2 → qN (red 2 (intMat R)) j = 0) ∧
    (HasSq1 R → qN (red 2 (intMat R)) 0 = qN (red 2 (intMat R)) 2) ∧
    (¬ HasSq1 R → qN (red 2 (intMat R)) 0 = 4 ^ dyDim R) := by
  classical
  set A := intMat R
  set K : Matrix (Fin (dyDim R)) (Fin (dyDim R)) ℤ := Matrix.of fun i j => A i j / 2
  have hA : A = (2 : ℤ) • K := by
    ext i j
    show intMat R i j = 2 * (Matrix.of (fun i j => intMat R i j / 2) i j)
    rw [Matrix.of_apply]
    rcases intMat_entry R i j with h | ⟨c, hc, i', j', h⟩
    · rw [h]; rfl
    · rw [Int.mul_ediv_cancel' (h ▸ bInt_even c (he c hc) i' j')]
  have hAs : Aᵀ = A := (isSymm_intMat R).eq
  have hKs : Kᵀ = K := by
    ext i j
    simp only [Matrix.transpose_apply, K, Matrix.of_apply]
    rw [show A j i = Aᵀ i j from rfl, hAs]
  have hq : ∀ y, qv (red 2 A) y = 2 * (y ⬝ᵥ fun i => ((K i i : ℤ) : ZMod (2 ^ 2))) := by
    intro y; rw [hA, red_smul, qv_smul]; push_cast; exact two_qv_K hKs y
  have hval : ∀ y, qv (red 2 A) y = 0 ∨ qv (red 2 A) y = 2 := by
    intro y; rw [hq]
    have := (show ∀ z : ZMod (2 ^ 2), 2 * z = 0 ∨ 2 * z = 2 by decide)
      (y ⬝ᵥ fun i => ((K i i : ℤ) : ZMod (2 ^ 2)))
    exact this
  refine ⟨fun j h0 h2 => ?_, fun hs => ?_, fun hs => ?_⟩
  · unfold qN
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y _ hy
    rcases hval y with h | h <;> rw [h] at hy
    · exact h0 hy.symm
    · exact h2 hy.symm
  · obtain ⟨c, hc, hsq, he1⟩ := hs
    obtain ⟨i₀, -⟩ : ∃ i₀ : Fin c.dim, True := by
      cases c with
      | sq e u => exact ⟨⟨0, Nat.one_pos⟩, trivial⟩
      | hyp e => exact absurd hsq id
      | ell e => exact absurd hsq id
    obtain ⟨k₀, hk₀⟩ := intMat_diag_of_mem R c hc i₀
    have hnot : ¬ (4 : ℤ) ∣ A k₀ k₀ := by
      show ¬ 4 ∣ intMat R k₀ k₀
      rw [hk₀]; exact (bInt_diag_high (hv c hc) (he c hc) i₀).mpr ⟨hsq, he1⟩
    have hKodd : ((K k₀ k₀ : ℤ) : ZMod (2 ^ 2)) * 2 = 2 := by
      have hAk : A k₀ k₀ = 2 * K k₀ k₀ := by rw [hA]; simp
      have hodd : ¬ 2 ∣ K k₀ k₀ := fun ⟨t, ht⟩ => hnot ⟨t, by rw [hAk, ht]; ring⟩
      obtain ⟨t, ht⟩ : ∃ t, K k₀ k₀ = 2 * t + 1 := ⟨K k₀ k₀ / 2, by omega⟩
      rw [ht]; push_cast
      ring_nf
      rw [show (4 : ZMod (2 ^ 2)) = 0 from rfl]; ring
    have hshift : ∀ y, qv (red 2 A) (y + Pi.single k₀ 1) = qv (red 2 A) y + 2 := by
      intro y
      rw [hq, hq, add_dotProduct, mul_add]
      congr 1
      rw [single_dotProduct, one_mul, mul_comm]; exact hKodd
    unfold qN
    refine Finset.card_bij (fun y _ => y + Pi.single k₀ 1) (fun y hy => ?_) (fun y _ y' _ h => ?_)
      (fun y hy => ⟨y - Pi.single k₀ 1, ?_, by simp⟩)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      rw [hshift, hy]; rfl
    · simpa using h
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      have := hshift (y - Pi.single k₀ 1)
      rw [sub_add_cancel, hy] at this
      have h2 : (2 : ZMod (2 ^ 2)) = qv (red 2 A) (y - Pi.single k₀ 1) + 2 := this
      calc qv (red 2 A) (y - Pi.single k₀ 1) = qv (red 2 A) (y - Pi.single k₀ 1) + 2 - 2 := by ring
        _ = 0 := by rw [← h2]; ring
  · have hK2 : ∀ k, (2 : ℤ) ∣ K k k := by
      intro k
      obtain ⟨c, hc, i, hci⟩ := intMat_diag R k
      have h4 : (4 : ℤ) ∣ A k k := by
        show 4 ∣ intMat R k k
        rw [hci]
        by_contra hn
        exact hs ⟨c, hc, ((bInt_diag_high (hv c hc) (he c hc) i).mp hn)⟩
      have hAk : A k k = 2 * K k k := by rw [hA]; simp
      obtain ⟨t, ht⟩ := h4
      exact ⟨t, by linarith⟩
    have hzero : ∀ y, qv (red 2 A) y = 0 := by
      intro y; rw [hq]
      unfold dotProduct
      rw [Finset.mul_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      obtain ⟨t, ht⟩ := hK2 k
      show 2 * (y k * ((K k k : ℤ) : ZMod (2 ^ 2))) = 0
      rw [ht]; push_cast
      rw [show (2 : ZMod (2 ^ 2)) * (y k * (2 * (t : ZMod (2 ^ 2)))) = (2 * 2) * (y k * t) by ring,
        show (2 : ZMod (2 ^ 2)) * 2 = 0 from rfl, zero_mul]
    unfold qN
    rw [Finset.filter_true_of_mem fun y _ => hzero y, Finset.card_univ]
    simp

/-! ### $p_B$ from the value counts -/

theorem pB_eq_qN {b : ℕ} (B : Matrix (Fin b) (Fin b) ℤ) : pB B = (qN (red 2 B) 0 : ℝ) / 4 ^ b := by
  classical
  have hcomp := card_comp_div (col4 b) (col4_surj b) (fun y => qv (red 2 B) y = 0)
  have hset : Nat.card {z : Matrix (Fin b) (Fin 1) (ZMod (2 ^ 3)) // (4 : ℤ) ∣ ((lift z)ᵀ * B * lift z) 0 0} =
      (Finset.univ.filter fun x => qv (red 2 B) (col4 b x) = 0).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1; ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [four_dvd_iff_cast, cast_quad_col]
  have hcardG : Fintype.card (Matrix (Fin b) (Fin 1) (ZMod (2 ^ 3))) = 8 ^ b := by
    rw [show Fintype.card (Matrix (Fin b) (Fin 1) (ZMod (2 ^ 3))) = Fintype.card (Fin b → Fin 1 → ZMod (2 ^ 3))
      from rfl, Fintype.card_fun, Fintype.card_fun]
    simp
  have hcardH : Fintype.card (Fin b → ZMod (2 ^ 2)) = 4 ^ b := by simp
  rw [hcardG, hcardH] at hcomp
  unfold pB
  rw [hset]
  unfold qN
  push_cast at hcomp ⊢
  have h8 : (8 : ℝ) ^ b ≠ 0 := by positivity
  have h4 : (4 : ℝ) ^ b ≠ 0 := by positivity
  rw [div_eq_div_iff h8 h4] at hcomp
  rw [div_eq_div_iff h8 h4]
  linarith

theorem zmod4_cases (j : ZMod (2 ^ 2)) : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by revert j; decide

theorem sum_zmod4 (f : ZMod (2 ^ 2) → ℕ) : ∑ k, f k = f 0 + f 1 + f 2 + f 3 := by
  rw [show (Finset.univ : Finset (ZMod (2 ^ 2))) = {0, 1, 2, 3} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

/-- Convolution with a count supported on $\{0, 2\}$, at $0$ and at $2$. -/
theorem conv_02 (X Y : ZMod (2 ^ 2) → ℕ) (hY : ∀ k, k ≠ 0 → k ≠ 2 → Y k = 0) :
    ∑ k, X k * Y (0 - k) = X 0 * Y 0 + X 2 * Y 2 ∧ ∑ k, X k * Y (2 - k) = X 2 * Y 0 + X 0 * Y 2 := by
  have h1 := hY 1 (by decide) (by decide)
  have h3 := hY 3 (by decide) (by decide)
  rw [sum_zmod4, sum_zmod4]
  rw [show (0 : ZMod (2 ^ 2)) - 0 = 0 from rfl, show (0 : ZMod (2 ^ 2)) - 1 = 3 from rfl,
    show (0 : ZMod (2 ^ 2)) - 2 = 2 from rfl, show (0 : ZMod (2 ^ 2)) - 3 = 1 from rfl,
    show (2 : ZMod (2 ^ 2)) - 0 = 2 from rfl, show (2 : ZMod (2 ^ 2)) - 1 = 1 from rfl,
    show (2 : ZMod (2 ^ 2)) - 2 = 0 from rfl, show (2 : ZMod (2 ^ 2)) - 3 = 3 from rfl, h1, h3]
  constructor <;> ring

theorem qN_nil (j : ZMod (2 ^ 2)) : qN (red 2 (intMat [])) j = if j = 0 then 1 else 0 := by
  unfold qN
  haveI : IsEmpty (Fin (dyDim [])) := inferInstanceAs (IsEmpty (Fin 0))
  have h0 : ∀ x : Fin (dyDim []) → ZMod (2 ^ 2), qv (red 2 (intMat [])) x = 0 := fun x => by
    simp [qv, dotProduct]
  simp only [h0]
  split_ifs with h
  · subst h; simp
  · simp [Ne.symm h]

theorem qN_unary_val : ∀ m j : ZMod (2 ^ 2), (m = 1 ∨ m = 3) →
    qN !![m] j = (if j = 0 then 2 else 0) + (if j = m then 2 else 0) := by decide

theorem qN_binary_val : ∀ m m' j : ZMod (2 ^ 2), (m = 1 ∨ m = 3) → (m' = 1 ∨ m' = 3) →
    qN !![m, 0; 0, m'] j = (if j = 0 then 4 else 0) + (if j = m then 4 else 0) + (if j = m' then 4 else 0) +
      (if j = m + m' then 4 else 0) := by decide

theorem zmod4_odd {w : ℤ} (hw : w = 1 ∨ w = 3 ∨ w = 5 ∨ w = 7) :
    ((w : ZMod (2 ^ 2)) = 1 ∨ (w : ZMod (2 ^ 2)) = 3) := by
  rcases hw with rfl | rfl | rfl | rfl <;> decide

theorem qN_sq_one {w : ℤ} (hw : w = 1 ∨ w = 3 ∨ w = 5 ∨ w = 7) (j : ZMod (2 ^ 2)) :
    qN (red 2 (intMat [DyBlock.sq 0 w])) j =
      (if j = 0 then 2 else 0) + (if j = (w : ZMod (2 ^ 2)) then 2 else 0) := by
  rw [qN_reidx (intMat_unary_reidx w)]
  have : red 2 (!![w] : Matrix (Fin 1) (Fin 1) ℤ) = !![(w : ZMod (2 ^ 2))] := by
    ext i j; fin_cases i; fin_cases j; simp
  rw [this]
  exact qN_unary_val _ _ (zmod4_odd hw)

theorem qN_sq_two {w w' : ℤ} (hw : w = 1 ∨ w = 3 ∨ w = 5 ∨ w = 7) (hw' : w' = 1 ∨ w' = 3 ∨ w' = 5 ∨ w' = 7)
    (j : ZMod (2 ^ 2)) :
    qN (red 2 (intMat [DyBlock.sq 0 w, DyBlock.sq 0 w'])) j =
      (if j = 0 then 4 else 0) + (if j = (w : ZMod (2 ^ 2)) then 4 else 0) +
        (if j = (w' : ZMod (2 ^ 2)) then 4 else 0) + (if j = (w : ZMod (2 ^ 2)) + w' then 4 else 0) := by
  have hr : Reidx (intMat [DyBlock.sq 0 w, DyBlock.sq 0 w']) (!![w, 0; 0, w'] : Matrix (Fin 2) (Fin 2) ℤ) :=
    ⟨finCongr rfl, by rw [intMat_sq_sq]; rfl⟩
  rw [qN_reidx hr]
  have : red 2 (!![w, 0; 0, w'] : Matrix (Fin 2) (Fin 2) ℤ) = !![(w : ZMod (2 ^ 2)), 0; 0, (w' : ZMod (2 ^ 2))] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [this]
  exact qN_binary_val _ _ _ (zmod4_odd hw) (zmod4_odd hw')

/-! ### $p_B$ for a normal form -/

theorem dyDim_app : ∀ L₁ L₂ : List DyBlock, dyDim (L₁ ++ L₂) = dyDim L₁ + dyDim L₂
  | [], L₂ => by simp [dyDim]
  | c :: L₁, L₂ => by simp [dyDim, dyDim_app L₁ L₂]; ring

theorem dyDim_sqList (e : ℤ) : ∀ ws : List ℤ, dyDim (sqList e ws) = ws.length
  | [] => rfl
  | w :: ws => by
    show 1 + dyDim (sqList e ws) = _
    rw [dyDim_sqList e ws]; simp; ring

theorem qN_append (L₁ L₂ : List DyBlock) (j : ZMod (2 ^ 2)) :
    qN (red 2 (intMat (L₁ ++ L₂))) j = ∑ k, qN (red 2 (intMat L₁)) k * qN (red 2 (intMat L₂)) (j - k) := by
  rw [qN_reidx (reidx_append L₁ L₂) j]
  rw [show red 2 (orthSumMat (intMat L₁) (intMat L₂)) = orthSumMat (red 2 (intMat L₁)) (red 2 (intMat L₂)) from
    orthSumMat_map _ (map_zero _) _ _]
  exact qN_orthSum _ _ j

theorem qN_total {n : ℕ} (V : Matrix (Fin n) (Fin n) (ZMod (2 ^ 2))) : ∑ j, qN V j = 4 ^ n := by
  classical
  unfold qN
  rw [← Finset.card_eq_sum_card_fiberwise (f := fun y => qv V y) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  simp

theorem qN_even_odd {E : List DyBlock} (hE : IsEvenList 0 E) :
    ∀ k : ZMod (2 ^ 2), k ≠ 0 → k ≠ 2 → qN (red 2 (intMat E)) k = 0 := by
  intro k h0 h2
  unfold qN
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro y _ hy
  obtain ⟨z, hz⟩ := qv_even (isSymm_intMat E).eq (isEvenList_evenDiag hE) y
  have := (show ∀ z : ZMod (2 ^ 2), 2 * z = 0 ∨ 2 * z = 2 by decide) z
  rw [hz] at hy
  rcases this with h | h <;> rw [h] at hy
  · exact h0 hy.symm
  · exact h2 hy.symm

theorem four_dvd_add_iff_zmod4 {w w' : ℤ} : (4 : ℤ) ∣ w + w' ↔ ((w : ZMod (2 ^ 2)) + w' = 0) := by
  rw [← Int.cast_add, ZMod.intCast_zmod_eq_zero_iff_dvd]; norm_num

theorem qN_sqList_one {w : ℤ} (hw : w = 1 ∨ w = 3 ∨ w = 5 ∨ w = 7) (j : ZMod (2 ^ 2)) :
    qN (red 2 (intMat (sqList 0 [w]))) j =
      (if j = 0 then 2 else 0) + (if j = (w : ZMod (2 ^ 2)) then 2 else 0) := qN_sq_one hw j

theorem qN_sqList_two {w w' : ℤ} (hw : w = 1 ∨ w = 3 ∨ w = 5 ∨ w = 7) (hw' : w' = 1 ∨ w' = 3 ∨ w' = 5 ∨ w' = 7)
    (j : ZMod (2 ^ 2)) :
    qN (red 2 (intMat (sqList 0 [w, w']))) j =
      (if j = 0 then 4 else 0) + (if j = (w : ZMod (2 ^ 2)) then 4 else 0) +
        (if j = (w' : ZMod (2 ^ 2)) then 4 else 0) + (if j = (w : ZMod (2 ^ 2)) + w' then 4 else 0) :=
  qN_sq_two hw hw' j

theorem qN_sqList {ws : List ℤ} (hws : ∀ w ∈ ws, w = 1 ∨ w = 3 ∨ w = 5 ∨ w = 7) (hlen : ws.length ≤ 2) :
    (qN (red 2 (intMat (sqList 0 ws))) 0 : ℝ) = (if ws.length = 0 then 1 else if ws.length = 1 then 2
      else if (4 : ℤ) ∣ ws.sum then 8 else 4) ∧
      (qN (red 2 (intMat (sqList 0 ws))) 2 : ℝ) = (if ws.length ≤ 1 then 0 else if (4 : ℤ) ∣ ws.sum then 0 else 4) := by
  match ws, hlen, hws with
  | [], _, _ =>
    have h0 : qN (red 2 (intMat (sqList 0 []))) 0 = 1 := by rw [show sqList 0 [] = [] from rfl, qN_nil]; rfl
    have h2 : qN (red 2 (intMat (sqList 0 []))) 2 = 0 := by rw [show sqList 0 [] = [] from rfl, qN_nil]; rfl
    rw [h0, h2]; simp
  | [w], _, hws =>
    have hw := hws w (by simp)
    rw [qN_sqList_one hw, qN_sqList_one hw]
    rcases zmod4_odd hw with h1 | h1 <;> rw [h1] <;> simp (config := { decide := true })
  | [w, w'], _, hws =>
    have hw := hws w (by simp)
    have hw' := hws w' (by simp)
    rw [qN_sqList_two hw hw', qN_sqList_two hw hw']
    simp only [List.length_cons, List.length_nil, List.sum_cons, List.sum_nil, add_zero, four_dvd_add_iff_zmod4]
    rcases zmod4_odd hw with h1 | h1 <;> rcases zmod4_odd hw' with h2 | h2 <;> rw [h1, h2] <;>
      simp (config := { decide := true })

open Classical in
/-- **$p_B$ for a normal form** $B = \langle w_0, \dots\rangle \perp E \perp R$: at most two blocks $w x^2$ of exponent
$0$, $E$ even unimodular of dimension $2t$ and sign $\varepsilon$, $R$ of positive exponents; $P = (1 +
\varepsilon 2^{-t})/2$. -/
theorem pB_normal {ws : List ℤ} (hws : ∀ w ∈ ws, w = 1 ∨ w = 3 ∨ w = 5 ∨ w = 7) (hlen : ws.length ≤ 2)
    {E : List DyBlock} (hE : IsEvenList 0 E) {R : List DyBlock} (hRv : ∀ c ∈ R, c.Valid)
    (hRe : ∀ c ∈ R, 1 ≤ blockExp c) :
    pB (intMat (sqList 0 ws ++ E ++ R)) =
      let P : ℝ := (1 + ((evenSign E).toInt : ℝ) * ((2 : ℝ) ^ E.length)⁻¹) / 2
      if HasSq1 R then (if ws = [] then 1 / 2 else 1 / 4)
      else (if ws.length = 0 then P else if ws.length = 1 then P / 2
        else if (4 : ℤ) ∣ ws.sum then P / 2 else 1 / 4) := by
  obtain ⟨hR0, hRs, hRn⟩ := qN_high hRv hRe
  have hEo := qN_even_odd hE
  obtain ⟨hE1, hE2⟩ := card_qv_zero_add (isSymm_intMat E).eq (isEvenList_evenDiag hE)
  have hg := gsum_intMat_even E hE
  have hdE : dyDim E = 2 * E.length := dyDim_even_list E fun c hc => (hE c hc).2
  rw [pB_eq_qN, qN_append (sqList 0 ws ++ E) R 0, (conv_02 _ _ hR0).1, qN_append (sqList 0 ws) E 0,
    qN_append (sqList 0 ws) E 2,
    (conv_02 _ _ hEo).1, (conv_02 _ _ hEo).2]
  have hdim : dyDim (sqList 0 ws ++ E ++ R) = ws.length + 2 * E.length + dyDim R := by
    rw [dyDim_app, dyDim_app, dyDim_sqList, hdE]
  rw [hdim]
  set A := qN (red 2 (intMat E)) 0
  set B := qN (red 2 (intMat E)) 2
  set t := E.length
  set h := dyDim R
  have hAB : (A : ℝ) + B = 4 ^ (2 * t) := by
    have : ((A + B : ℕ) : ℤ) = 4 ^ dyDim E := by push_cast; exact hE2
    rw [hdE] at this; exact_mod_cast this
  have hAmB : (A : ℝ) - B = ((evenSign E).toInt : ℝ) * 8 ^ t := by
    have : (A : ℤ) - B = (evenSign E).toInt * 8 ^ t := hE1.trans hg
    exact_mod_cast this
  have hRtot := qN_total (red 2 (intMat R))
  rw [sum_zmod4, hR0 1 (by decide) (by decide), hR0 3 (by decide) (by decide)] at hRtot
  have h4t : (4 : ℝ) ^ (2 * t) = ((2 : ℝ) ^ t) ^ 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]; ring_nf
  have h8t : (8 : ℝ) ^ t = ((2 : ℝ) ^ t) ^ 3 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_mul]; ring_nf
  have hX : (0 : ℝ) < 2 ^ t := by positivity
  have hA : (A : ℝ) = ((2 : ℝ) ^ t) ^ 3 * (2 ^ t + (evenSign E).toInt) / 2 := by
    rw [h4t] at hAB; rw [h8t] at hAmB
    field_simp; linarith
  have hB : (B : ℝ) = ((2 : ℝ) ^ t) ^ 3 * (2 ^ t - (evenSign E).toInt) / 2 := by
    rw [h4t] at hAB; rw [h8t] at hAmB
    field_simp; linarith
  simp only
  obtain ⟨hS0, hS2⟩ := qN_sqList hws hlen
  push_cast
  rw [hS0, hS2, hA, hB]
  by_cases hs : HasSq1 R
  · have hR02 := hRs hs
    have hRh : (qN (red 2 (intMat R)) 0 : ℝ) = 4 ^ h / 2 := by
      have : (qN (red 2 (intMat R)) 0 : ℝ) + qN (red 2 (intMat R)) 2 = 4 ^ h := by
        have h' : qN (red 2 (intMat R)) 0 + qN (red 2 (intMat R)) 2 = 4 ^ h := by simpa using hRtot
        exact_mod_cast h'
      rw [← hR02] at this; linarith
    rw [if_pos hs, ← hR02, hRh]
    have h4p : (4 : ℝ) ^ (ws.length + 2 * t + h) = 4 ^ ws.length * ((2 : ℝ) ^ t) ^ 4 * 4 ^ h := by
      rw [pow_add, pow_add, h4t]
    rw [h4p]
    match ws, hlen with
    | [], _ => simp; field_simp; ring
    | [w], _ => simp; field_simp; ring
    | [w, w'], _ =>
      by_cases hd : (4 : ℤ) ∣ w + w'
      · simp [hd]; field_simp; ring
      · simp [hd]; field_simp; ring
  · have hR2 : (qN (red 2 (intMat R)) 2 : ℝ) = 0 := by
      have := hRtot; rw [hRn hs] at this
      have : qN (red 2 (intMat R)) 2 = 0 := by omega
      exact_mod_cast this
    rw [if_neg hs, hR2, hRn hs]
    have h4p : (4 : ℝ) ^ (ws.length + 2 * t + h) = 4 ^ ws.length * ((2 : ℝ) ^ t) ^ 4 * 4 ^ h := by
      rw [pow_add, pow_add, h4t]
    push_cast
    rw [h4p]
    match ws, hlen with
    | [], _ => simp; field_simp; ring
    | [w], _ => simp; field_simp; ring
    | [w, w'], _ =>
      by_cases hd : (4 : ℤ) ∣ w + w'
      · simp [hd]; field_simp; ring
      · simp [hd]; field_simp; ring

/-! ### $p_B$ from the symbol of $B$ -/

theorem qN_congr {n : ℕ} {V G : Matrix (Fin n) (Fin n) (ZMod (2 ^ 2))} (hG : IsUnit G) (j : ZMod (2 ^ 2)) :
    qN (Gᵀ * V * G) j = qN V j := by
  obtain ⟨u, rfl⟩ := hG
  unfold qN
  refine Finset.card_bij (fun y _ => (u : Matrix (Fin n) (Fin n) (ZMod (2 ^ 2))) *ᵥ y) (fun y hy => ?_)
    (fun y _ y' _ h => ?_) (fun y hy => ⟨(↑u⁻¹ : Matrix (Fin n) (Fin n) (ZMod (2 ^ 2))) *ᵥ y, ?_, ?_⟩)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢; rwa [← qv_congr]
  · have := congrArg (fun z => (↑u⁻¹ : Matrix (Fin n) (Fin n) (ZMod (2 ^ 2))) *ᵥ z) h
    simpa [Matrix.mulVec_mulVec] using this
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    rw [qv_congr, Matrix.mulVec_mulVec]; simpa using hy
  · simp [Matrix.mulVec_mulVec]

theorem qN_eq_of_zpEquiv {n : ℕ} {A A' : Matrix (Fin n) (Fin n) ℤ}
    (h : ZpEquiv (A.map (Int.cast : ℤ → ℚ_[2])) (A'.map (Int.cast : ℤ → ℚ_[2]))) (j : ZMod (2 ^ 2)) :
    qN (red 2 A') j = qN (red 2 A) j := by
  obtain ⟨G, hG, hGe⟩ := exists_unit_congr_of_zpEquiv (p := 2) h 2
  change qN (A'.map (Int.castRingHom (ZMod (2 ^ 2)))) j = qN (A.map (Int.castRingHom (ZMod (2 ^ 2)))) j
  rw [← hGe]
  exact qN_congr hG j

theorem pB_eq_of_blockSymbol_eq {H H' : List DyBlock} (hH : ∀ b ∈ H, b.Valid) (hH0 : ∀ b ∈ H, 0 ≤ blockExp b)
    (hH' : ∀ b ∈ H', b.Valid) (hH'0 : ∀ b ∈ H', 0 ≤ blockExp b) (hn : dyDim H' = dyDim H)
    (hσ : blockSymbol H = blockSymbol H') : pB (intMat H) = pB (intMat H') := by
  rw [pB_eq_qN, pB_eq_qN, ← qN_eq_of_zpEquiv (zpEquiv_of_blockSymbol_eq hH hH0 hH' hH'0 hn hσ),
    qN_reidx (reidx_cast hn.symm _)]
  have h4 : (4 : ℝ) ^ dyDim H = 4 ^ dyDim H' := by rw [hn]
  rw [h4]

/-- **$p_B$ from the symbol** $\sigma$ of $B$ ($f_2 = \sigma_0$, $f_4 = \sigma_1$). -/
noncomputable def pBsym (σ : TwoSymbol) : ℝ :=
  if (σ 0).type = .II then (if (σ 1).type = .I then 1 / 2 else (pII (σ 0) : ℝ))
  else (if (σ 1).type = .I then 1 / 4 else (rI (σ 0) : ℝ) / 4)

theorem hasSq1_iff {R : List DyBlock} (hRe : ∀ c ∈ R, 1 ≤ blockExp c) :
    HasSq1 R ↔ (blockF (R.filter fun c => blockExp c = 1)).type = .I := by
  unfold HasSq1 blockF
  simp only
  constructor
  · rintro ⟨c, hc, hsq, he⟩
    rw [if_pos]
    rw [List.any_eq_true]
    exact ⟨c, List.mem_filter.mpr ⟨hc, by simp [he]⟩, by simpa using hsq⟩
  · intro h
    by_contra hn
    rw [if_neg] at h
    · exact absurd h (by decide)
    · rw [Bool.not_eq_true, List.any_eq_false]
      intro c hc hsq
      have hc' := List.mem_filter.mp hc
      exact hn ⟨c, hc'.1, by simpa using hsq, by simpa using hc'.2⟩

/-- **$p_B$ for every block decomposition $B$ of nonnegative exponents.** -/
@[kb "conwaysloane1988" "(3), p. 263; Table 1, p. 264 (p = 2, the proportion p_B)"]
theorem pB_intMat {H : List DyBlock} (hv : ∀ c ∈ H, c.Valid) (he : ∀ c ∈ H, 0 ≤ blockExp c) :
    pB (intMat H) = pBsym (blockSymbol H) := by
  classical
  set Hz := H.filter fun c => blockExp c = 0
  set Hp := H.filter fun c => ¬ (blockExp c = 0)
  have hperm : H.Perm (Hz ++ Hp) := by
    have := List.filter_append_perm (fun c => decide (blockExp c = 0)) H
    simpa [Hz, Hp] using this.symm
  have hvz : ∀ c ∈ Hz, c.Valid := fun c hc => hv c (List.mem_filter.mp hc).1
  have hez : ∀ c ∈ Hz, blockExp c = 0 := fun c hc => by simpa using (List.mem_filter.mp hc).2
  have hvp : ∀ c ∈ Hp, c.Valid := fun c hc => hv c (List.mem_filter.mp hc).1
  have hep : ∀ c ∈ Hp, 1 ≤ blockExp c := fun c hc => by
    have h1 := he c (List.mem_filter.mp hc).1
    have h2 : ¬ blockExp c = 0 := by simpa using (List.mem_filter.mp hc).2
    omega
  obtain ⟨ws, E, hws, hE, hlen, -, hF⟩ := exists_normal 0 Hz hvz hez
  set H' := sqList 0 ws ++ E ++ Hp
  have hv' : ∀ c ∈ H', c.Valid := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · rcases List.mem_append.mp hc with hc | hc
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hc; exact hws w hw
      · exact isEvenList_valid hE c hc
    · exact hvp c hc
  have he' : ∀ c ∈ H', 0 ≤ blockExp c := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · rcases List.mem_append.mp hc with hc | hc
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hc; exact le_refl _
      · exact (hE c hc).1.ge
    · exact (hep c hc).trans' (by norm_num)
  have hP0 : ∀ c ∈ sqList 0 ws ++ E, blockExp c = 0 := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hc; rfl
    · exact (hE c hc).1
  have hσ : blockSymbol H = blockSymbol H' := by
    rw [blockSymbol_perm hperm]
    exact blockSymbol_congr_prefix hez hP0 hF Hp
  have hn : dyDim H' = dyDim H := by
    have h1 := congrArg TwoFactor.dim hF
    simp only [blockF, List.map_append, List.sum_append] at h1
    rw [dyDim_eq_sum, dyDim_eq_sum, (hperm.map DyBlock.dim).sum_eq]
    simp only [H', List.map_append, List.sum_append]
    omega
  rw [pB_eq_of_blockSymbol_eq hv he hv' he' hn hσ, hσ, pB_normal hws hlen hE hvp hep]
  -- the symbol of `H'`
  have hS0 : blockSymbol H' 0 = blockF (sqList 0 ws ++ E) := by
    rw [blockSymbol_eq_blockF, List.filter_append,
      List.filter_eq_self.mpr fun c hc => by simp [hP0 c hc],
      List.filter_eq_nil_iff.mpr fun c hc => by have := hep c hc; simp; omega, List.append_nil]
  have hS1 : (blockSymbol H' 1).type = .I ↔ HasSq1 Hp := by
    rw [hasSq1_iff hep, blockSymbol_eq_blockF, List.filter_append,
      List.filter_eq_nil_iff.mpr fun c hc => by simp [hP0 c hc], List.nil_append]
    rfl
  unfold pBsym
  rw [hS0]
  simp only
  by_cases h4 : HasSq1 Hp
  · rw [if_pos h4, if_pos (hS1.mpr h4), if_pos (hS1.mpr h4)]
    match ws, hlen, hws with
    | [], _, _ =>
      have : (blockF (sqList 0 [] ++ E)).type = .II := by
        show (blockF E).type = .II; rw [blockF_even hE]
      simp [this]
    | [w], _, hws =>
      have : (blockF (sqList 0 [w] ++ E)).type = .I := by
        show (blockF (DyBlock.sq 0 w :: E)).type = .I; rw [blockF_cons_sq]
      simp [this]
    | [w, w'], _, hws =>
      have : (blockF (sqList 0 [w, w'] ++ E)).type = .I := by
        show (blockF (DyBlock.sq 0 w :: DyBlock.sq 0 w' :: E)).type = .I; rw [blockF_cons_sq]
      simp [this]
  · have hn4 : ¬ (blockSymbol H' 1).type = .I := fun h => h4 (hS1.mp h)
    rw [if_neg h4, if_neg hn4, if_neg hn4]
    match ws, hlen, hws with
    | [], _, _ =>
      have : (blockF (sqList 0 [] ++ E)) = ⟨2 * E.length, evenSign E, .II, 0⟩ := blockF_even hE
      rw [this]
      simp [pII, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    | [w], _, hws =>
      have hw := hws w (by simp)
      have hb : blockF (sqList 0 [w] ++ E) = blockF (DyBlock.sq 0 w :: E) := rfl
      have ht : (blockF (DyBlock.sq 0 w :: E)).type = .I := by rw [blockF_cons_sq]
      rw [hb]
      simp [ht, rI_odd hw hE]
      ring
    | [w, w'], _, hws =>
      have hw := hws w (by simp)
      have hw' := hws w' (by simp)
      have hb : blockF (sqList 0 [w, w'] ++ E) = blockF (DyBlock.sq 0 w :: DyBlock.sq 0 w' :: E) := rfl
      have ht : (blockF (DyBlock.sq 0 w :: DyBlock.sq 0 w' :: E)).type = .I := by rw [blockF_cons_sq]
      rw [hb]
      by_cases hd : (4 : ℤ) ∣ w + w'
      · simp [ht, rI_even hw hw' hE, hd]; ring
      · simp [ht, rI_even hw hw' hE, hd]

end QuadFormsKB.ConwaySloane.Mass.Two
