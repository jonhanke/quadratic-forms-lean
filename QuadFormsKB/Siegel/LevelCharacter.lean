/-
# Level, discriminant and quadratic character of an integral quadratic form (stage A)

For an integral form $Q$ in $n$ variables with Hessian $H$ (even symmetric, $Q(\vec{x}) = \tfrac12\vec{x}^{\mathsf T}H\vec{x}$):

* `IsEvenSymm`: integral symmetric matrices with even diagonal; closed under congruence (`IsEvenSymm.conj`).
* `det_mod_four`: if $H$ is even symmetric of even size $n = 2k$, then $(-1)^k\det H \equiv 0, 1 \pmod 4$;
  `det_even_of_odd`: of odd size, $\det H$ is even.
* `IsLevel Q N`: $N H^{-1}$ is an even symmetric integral matrix; `level Q` is the least such $N \ge 1$
  (Hanke 2004, p. 355). Facts: `isLevel_iff_level_dvd` (the levels are the multiples of `level Q`),
  `isLevel_iff_isThetaLevel` (agreement with `IsThetaLevel`), `level_dvd_two_mul_det`, `level_dvd_det`
  (even $n$), `det_dvd_level_pow`, `prime_dvd_level_iff` (Hanke's Lemma 2.2 over $\mathbb{Q}$), `four_dvd_level`
  (odd $n$), `level_eq_of_intEquiv` (class invariance).
* `disc Q` $= (-1)^{\lfloor n/2\rfloor}\det H$ and `disc_mod_four` (even $n$).
* `chi Q b` $= \left(\frac{\Delta}{b}\right)$ (Jacobi symbol, $b$ odd), periodic modulo $4N$ (`chi_eq_of_modEq`), and the
  Dirichlet character `chiChar Q` modulo $4N$. For positive definite $Q$ of even rank the **canonical** character is
  `chiCharLevel` (modulo $N$ itself) in `ThetaCharacter.lean`, which reconciles all of these (stage B).
* Sanity checks (stage E): levels and characters of $E_8$, $I_2$, $I_3$, $I_4$, $A_2 \oplus A_2$ and
  $x_0^2 + x_1^2 + x_2^2 + 2x_3^2$.

Sources: Hanke 2004, p. 355 (level), p. 357 (character, even $n$), Lemma 2.2 (primes dividing $N$).
-/
import QuadFormsKB.Siegel.ThetaModular
import QuadFormsKB.Siegel.Genus
import QuadFormsKB.Siegel.E8
import QuadFormsKB.Siegel.FourSquares

open Matrix
open QuadFormsKB.Analysis (quadAt)

namespace QuadFormsKB.Siegel

/-! ### Even symmetric matrices -/

section EvenSymm

variable {ι κ : Type*}

/-- **Even symmetric integral matrix:** $W^{\mathsf T} = W$ and every diagonal entry $W_{ii}$ is even. Hessians of
integral forms are of this kind (`hessian_isEvenSymm`). -/
def IsEvenSymm (W : Matrix ι ι ℤ) : Prop := Wᵀ = W ∧ ∀ i, Even (W i i)

theorem isEvenSymm_add_transpose (V : Matrix ι ι ℤ) : IsEvenSymm (V + Vᵀ) :=
  ⟨by rw [transpose_add, transpose_transpose, add_comm], fun i => ⟨V i i, by simp⟩⟩

/-- An even symmetric matrix is $V + V^{\mathsf T}$ for an integral $V$ (strict upper part plus half the diagonal). -/
theorem IsEvenSymm.exists_eq_add_transpose [LinearOrder ι] {W : Matrix ι ι ℤ} (h : IsEvenSymm W) :
    ∃ V : Matrix ι ι ℤ, W = V + Vᵀ := by
  refine ⟨Matrix.of fun i j => if i < j then W i j else if i = j then W i i / 2 else 0, ?_⟩
  ext i j
  simp only [Matrix.add_apply, transpose_apply, of_apply]
  rcases lt_trichotomy i j with hij | rfl | hij
  · simp [hij, not_lt.2 hij.le, hij.ne']
  · obtain ⟨a, ha⟩ := h.2 i
    simp [ha]; omega
  · have hs : W j i = W i j := congrFun (congrFun h.1 i) j
    simp [hij, hij.ne', not_lt.2 hij.le, hs]

theorem IsEvenSymm.sub {W W' : Matrix ι ι ℤ} (h : IsEvenSymm W) (h' : IsEvenSymm W') :
    IsEvenSymm (W - W') :=
  ⟨by rw [transpose_sub, h.1, h'.1], fun i => by simpa using (h.2 i).sub (h'.2 i)⟩

theorem IsEvenSymm.smul {W : Matrix ι ι ℤ} (h : IsEvenSymm W) (c : ℤ) : IsEvenSymm (c • W) :=
  ⟨by rw [transpose_smul, h.1], fun i => by simpa using (h.2 i).mul_left c⟩

theorem IsEvenSymm.submatrix {W : Matrix ι ι ℤ} (h : IsEvenSymm W) (f : κ → ι) :
    IsEvenSymm (W.submatrix f f) :=
  ⟨by rw [transpose_submatrix, h.1], fun i => h.2 (f i)⟩

/-- **Congruence preserves evenness:** if $W$ is even symmetric then so is $PWP^{\mathsf T}$ for every integral
(possibly rectangular) $P$. *Proof:* $W = V + V^{\mathsf T}$, so $PWP^{\mathsf T} = PVP^{\mathsf T} + (PVP^{\mathsf T})^{\mathsf T}$. -/
theorem IsEvenSymm.conj [Fintype κ] [LinearOrder κ] {W : Matrix κ κ ℤ} (h : IsEvenSymm W) (P : Matrix ι κ ℤ) :
    IsEvenSymm (P * W * Pᵀ) := by
  obtain ⟨V, rfl⟩ := h.exists_eq_add_transpose
  have : P * (V + Vᵀ) * Pᵀ = P * V * Pᵀ + (P * V * Pᵀ)ᵀ := by
    simp [Matrix.mul_add, Matrix.add_mul, transpose_mul, Matrix.mul_assoc]
  rw [this]; exact isEvenSymm_add_transpose _

end EvenSymm

variable {n : ℕ}

/-- The Hessian $H = C + C^{\mathsf T}$ of an integral form is even symmetric. -/
theorem hessian_isEvenSymm (Q : QuadForm ℤ n) : IsEvenSymm Q.hessian := by
  unfold QuadForm.hessian; exact isEvenSymm_add_transpose _

/-! ### The determinant of an even symmetric matrix modulo 4 -/

/-- $x \equiv 0$ or $1 \pmod 4$ (the squares modulo 4). -/
def IsSqMod4 (x : ℤ) : Prop := (x : ZMod 4) = 0 ∨ (x : ZMod 4) = 1

/-- A permutation of `Fin (k + 2)` sending $0 \mapsto i$ and $1 \mapsto j$, for $i \ne j$. -/
private lemma exists_perm_zero_one {k : ℕ} {i j : Fin (k + 2)} (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin (k + 2)), σ 0 = i ∧ σ 1 = j := by
  obtain ⟨j', hj'⟩ : ∃ j', j' = Equiv.swap 0 i j := ⟨_, rfl⟩
  have hj'0 : j' ≠ 0 := by
    intro h
    have h2 : Equiv.swap 0 i j' = Equiv.swap 0 i 0 := by rw [h]
    rw [hj', Equiv.swap_apply_self, Equiv.swap_apply_left] at h2
    exact hij h2.symm
  refine ⟨Equiv.swap 0 i * Equiv.swap 1 j', ?_, ?_⟩
  · simp only [Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (by simp) (Ne.symm hj'0), Equiv.swap_apply_left]
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    rw [hj', Equiv.swap_apply_self]

/-- **The determinant of an even symmetric matrix modulo 4** (both parities at once): for $H$ even symmetric of
size $n$,
* if $n = 2k$ is even, $(-1)^k \det H \equiv 0$ or $1 \pmod 4$;
* if $n$ is odd, $\det H$ is even.

*Proof* (induction on $n$, removing two coordinates). If every entry of $H$ is even, $H = 2H'$ and
$2^n \mid \det H$. Otherwise some off-diagonal $H_{ij}$ is odd; move it to position $(0, 1)$ and write
$H = \begin{pmatrix} A & B \\ B^{\mathsf T} & D\end{pmatrix}$ with $A$ the $2 \times 2$ block, $\delta = \det A \equiv -1 \pmod 4$. Then
$$H \begin{pmatrix} \operatorname{adj} A & -\operatorname{adj}A\,B \\ 0 & \delta I\end{pmatrix}
= \begin{pmatrix} \delta I & 0 \\ B^{\mathsf T}\operatorname{adj}A & D' \end{pmatrix},\qquad
D' = \delta D - B^{\mathsf T}(\operatorname{adj}A)B,$$
so $\delta^{n-1}\det H = \delta^2 \det D'$, and $D'$ is even symmetric of size $n - 2$ (`IsEvenSymm.conj`). -/
theorem det_mod_four_aux (n : ℕ) : ∀ H : Matrix (Fin n) (Fin n) ℤ, IsEvenSymm H →
    (Even n → IsSqMod4 ((-1) ^ (n / 2) * H.det)) ∧ (Odd n → Even H.det) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H hH
  match n, ih, H, hH with
  | 0, _, H, _ => exact ⟨fun _ => Or.inr (by simp), fun h => absurd h (by decide)⟩
  | 1, _, H, hH => exact ⟨fun h => absurd h (by decide), fun _ => by rw [det_unique]; exact hH.2 _⟩
  | k + 2, ih, H, hH =>
    by_cases hall : ∀ i j, Even (H i j)
    · -- every entry even: $H = 2H'$
      have hH2 : H = (2 : ℤ) • Matrix.of (fun i j => H i j / 2) := by
        ext i j; obtain ⟨a, ha⟩ := hall i j; simp [ha]; omega
      have hdet : H.det = 2 ^ (k + 2) * (Matrix.of fun i j => H i j / 2).det := by
        conv_lhs => rw [hH2]
        rw [det_smul, Fintype.card_fin]
      refine ⟨fun _ => Or.inl ?_, fun _ => ?_⟩
      · rw [hdet]; push_cast
        rw [pow_add, show (2 : ZMod 4) ^ 2 = 0 from rfl]; ring
      · rw [hdet]; exact (Int.even_pow.2 ⟨even_two, by omega⟩).mul_right _
    · simp only [not_forall] at hall
      obtain ⟨i, j, hodd⟩ := hall
      have hij : i ≠ j := by rintro rfl; exact hodd (hH.2 i)
      obtain ⟨σ, hσ0, hσ1⟩ := exists_perm_zero_one hij
      let e : Fin 2 ⊕ Fin k ≃ Fin (k + 2) := finSumFinEquiv.trans (finCongr (add_comm 2 k))
      have he0 : e (Sum.inl 0) = 0 := Fin.ext (by simp [e])
      have he1 : e (Sum.inl 1) = 1 := Fin.ext (by simp [e])
      set G := H.submatrix (e.trans σ) (e.trans σ) with hGdef
      have hG : IsEvenSymm G := hH.submatrix _
      have hdetG : G.det = H.det := det_submatrix_equiv_self (e.trans σ) H
      set A := G.toBlocks₁₁
      set B := G.toBlocks₁₂
      set C := G.toBlocks₂₁
      set D := G.toBlocks₂₂
      have hGb : fromBlocks A B C D = G := fromBlocks_toBlocks G
      have hA : IsEvenSymm A := hG.submatrix Sum.inl
      have hD : IsEvenSymm D := hG.submatrix Sum.inr
      have hCB : C = Bᵀ := by
        ext x a; exact (congrFun (congrFun hG.1 (Sum.inr x)) (Sum.inl a)).symm
      have hA01 : Odd (A 0 1) := by
        have : A 0 1 = H i j := by
          simp only [A, G, toBlocks₁₁, of_apply, submatrix_apply, Equiv.trans_apply, he0, he1, hσ0, hσ1]
        rw [this]; exact Int.not_even_iff_odd.1 hodd
      have hA10 : A 1 0 = A 0 1 := congrFun (congrFun hA.1 0) 1
      set δ := A.det with hδdef
      have hδ2 : δ = A 0 0 * A 1 1 - A 0 1 * A 0 1 := by rw [hδdef, det_fin_two, hA10]
      have hδodd : Odd δ := by
        rw [hδ2]; exact (((hA.2 0).mul_right _)).sub_odd (hA01.mul hA01)
      have hδ4 : (δ : ZMod 4) = 3 := by
        obtain ⟨a, ha⟩ := hA.2 0
        obtain ⟨c, hc⟩ := hA.2 1
        obtain ⟨b, hb⟩ := hA01
        have : δ = 4 * (a * c - b * b - b - 1) + 3 := by rw [hδ2, ha, hc, hb]; ring
        rw [this]; push_cast; rw [show (4 : ZMod 4) = 0 from rfl]; ring
      set adjA := adjugate A with hadjdef
      have hadj : IsEvenSymm adjA := by
        refine ⟨by rw [adjugate_transpose, hA.1], fun a => ?_⟩
        rw [hadjdef, adjugate_fin_two]
        fin_cases a
        · simpa using hA.2 1
        · simpa using hA.2 0
      set D' := δ • D - C * adjA * B with hD'def
      have hD' : IsEvenSymm D' := by
        refine (hD.smul δ).sub ?_
        have := hadj.conj Bᵀ
        rwa [transpose_transpose, ← hCB] at this
      have key : G.det * (δ * δ ^ k) = δ ^ 2 * D'.det := by
        have hmul : G * fromBlocks adjA (-(adjA * B)) 0 (δ • (1 : Matrix (Fin k) (Fin k) ℤ)) =
            fromBlocks (δ • (1 : Matrix (Fin 2) (Fin 2) ℤ)) 0 (C * adjA) D' := by
          rw [← hGb, fromBlocks_multiply]
          congr 1
          · rw [mul_adjugate, Matrix.mul_zero, add_zero]
          · rw [Matrix.mul_neg, ← Matrix.mul_assoc, mul_adjugate, Matrix.mul_smul, Matrix.mul_one,
              Matrix.smul_mul, Matrix.one_mul, ← hδdef, neg_add_cancel]
          · rw [Matrix.mul_zero, add_zero]
          · rw [hD'def, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_neg, ← Matrix.mul_assoc]; abel
        have := congrArg det hmul
        rw [det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂, det_adjugate, det_smul, det_smul,
          det_one, det_one] at this
        simpa [Fintype.card_fin] using this
      refine ⟨fun hev => ?_, fun hod => ?_⟩
      · obtain ⟨m, hm⟩ : Even k := by simpa [Nat.even_add] using hev
        have ihk := (ih k (by omega) D' hD').1 ⟨m, hm⟩
        have key4 : ((G.det : ℤ) : ZMod 4) * ((δ : ZMod 4) * (δ : ZMod 4) ^ k) =
            (δ : ZMod 4) ^ 2 * (D'.det : ZMod 4) := by exact_mod_cast congrArg (Int.cast : ℤ → ZMod 4) key
        have h3k : (3 : ZMod 4) ^ k = 1 := by rw [hm, ← two_mul, pow_mul, show (3 : ZMod 4) ^ 2 = 1 from rfl, one_pow]
        rw [hδ4, h3k, show (3 : ZMod 4) ^ 2 = 1 from rfl] at key4
        have hk2 : (k + 2) / 2 = m + 1 := by omega
        have hk : k / 2 = m := by omega
        rw [hk] at ihk
        rw [hk2, ← hdetG]
        have h4 : (4 : ZMod 4) = 0 := rfl
        have heq : (((-1) ^ (m + 1) * G.det : ℤ) : ZMod 4) = (((-1) ^ m * D'.det : ℤ) : ZMod 4) := by
          simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
          linear_combination ((-1 : ZMod 4) ^ m) * key4 - ((-1 : ZMod 4) ^ m * (G.det : ZMod 4)) * h4
        unfold IsSqMod4 at ihk ⊢; rw [heq]; exact ihk
      · have hk : Odd k := by
          rcases Nat.even_or_odd k with h | h
          · exact absurd hod (Nat.not_odd_iff_even.2 (by simpa [Nat.even_add] using h))
          · exact h
        have hev := (ih k (by omega) D' hD').2 hk
        have h1 : Even (G.det * (δ * δ ^ k)) := by rw [key]; exact hev.mul_left _
        rw [← hdetG]
        exact (Int.even_mul.1 h1).resolve_right (Int.not_even_iff_odd.2 (hδodd.mul (hδodd.pow)))

/-- For $H$ even symmetric of even size $n = 2k$:
$(-1)^k\det H \equiv 0$ or $1 \pmod 4$. -/
theorem det_mod_four {n : ℕ} (hn : Even n) {H : Matrix (Fin n) (Fin n) ℤ} (hH : IsEvenSymm H) :
    IsSqMod4 ((-1) ^ (n / 2) * H.det) :=
  (det_mod_four_aux n H hH).1 hn

/-- An even symmetric integral matrix of odd size has even determinant. -/
theorem det_even_of_odd {n : ℕ} (hn : Odd n) {H : Matrix (Fin n) (Fin n) ℤ} (hH : IsEvenSymm H) :
    Even H.det :=
  (det_mod_four_aux n H hH).2 hn

/-! ### The level -/

/-- **$N$ is a level of $Q$** (Hanke 2004, p. 355, for $F = \mathbb{Q}$): $N H^{-1}$ is an even symmetric integral
matrix, i.e. there is an integral $W$ with $HW = N I$, $W^{\mathsf T} = W$ and even diagonal (then $W = NH^{-1}$ when
$\det H \ne 0$). Equivalently $N Q^*$ is integral-valued, $Q^*(\vec{y}) = \tfrac12 \vec{y}^{\mathsf T}H^{-1}\vec{y}$
(`isLevel_iff_isThetaLevel`). Hanke writes $N(2Q)^{-1}$ with $Q$ his Gram matrix, so $2Q = H$. -/
@[kb "hanke2004" "p. 355 (level N_Q)"]
def IsLevel (Q : QuadForm ℤ n) (N : ℕ) : Prop :=
  ∃ W : Matrix (Fin n) (Fin n) ℤ, Q.hessian * W = (N : ℤ) • 1 ∧ IsEvenSymm W

theorem isLevel_zero (Q : QuadForm ℤ n) : IsLevel Q 0 :=
  ⟨0, by simp, ⟨by simp, fun _ => by simp⟩⟩

theorem IsLevel.mul {Q : QuadForm ℤ n} {N : ℕ} (h : IsLevel Q N) (c : ℕ) : IsLevel Q (c * N) := by
  obtain ⟨W, hW, hE⟩ := h
  exact ⟨(c : ℤ) • W, by rw [Matrix.mul_smul, hW, smul_smul, Nat.cast_mul], hE.smul _⟩

theorem IsLevel.sub {Q : QuadForm ℤ n} {a b : ℕ} (ha : IsLevel Q a) (hb : IsLevel Q b) (hba : b ≤ a) :
    IsLevel Q (a - b) := by
  obtain ⟨W, hW, hE⟩ := ha
  obtain ⟨W', hW', hE'⟩ := hb
  exact ⟨W - W', by rw [Matrix.mul_sub, hW, hW', ← sub_smul, Nat.cast_sub hba], hE.sub hE'⟩

theorem IsLevel.mod {Q : QuadForm ℤ n} {a b : ℕ} (ha : IsLevel Q a) (hb : IsLevel Q b) :
    IsLevel Q (a % b) := by
  have h := ha.sub (hb.mul (a / b)) (by rw [mul_comm]; exact Nat.mul_div_le a b)
  rwa [mul_comm, ← Nat.mod_eq_sub_mul_div] at h

/-- The adjugate of a symmetric matrix is symmetric. -/
private lemma adjugate_symm {H : Matrix (Fin n) (Fin n) ℤ} (hH : Hᵀ = H) : (adjugate H)ᵀ = adjugate H := by
  rw [adjugate_transpose, hH]

/-- **$2|\det H|$ is a level** ($W = \pm 2\operatorname{adj} H$). -/
theorem isLevel_two_mul_natAbs_det (Q : QuadForm ℤ n) : IsLevel Q (2 * Q.hessian.det.natAbs) := by
  refine ⟨(2 * Q.hessian.det.sign) • adjugate Q.hessian, ?_, ?_, fun i => ?_⟩
  · rw [Matrix.mul_smul, mul_adjugate, smul_smul, Nat.cast_mul, ← Int.sign_mul_self, Nat.cast_ofNat]
    ring_nf
  · rw [transpose_smul, adjugate_symm (hessian_isEvenSymm Q).1]
  · rw [Matrix.smul_apply, smul_eq_mul, mul_assoc]; exact even_two_mul _

/-- **Diagonal of the adjugate (even size):** if $H$ is even symmetric of even size, then the diagonal entries of
$\operatorname{adj} H$ (principal minors of odd size $n - 1$) are even (`det_even_of_odd`). -/
theorem adjugate_diag_even (hn : Even n) {H : Matrix (Fin n) (Fin n) ℤ} (hH : IsEvenSymm H) (i : Fin n) :
    Even (adjugate H i i) := by
  cases n with
  | zero => exact i.elim0
  | succ m =>
    rw [adjugate_fin_succ_eq_det_submatrix]
    have hm : Odd m := by
      rcases Nat.even_or_odd m with h | h
      · exact absurd hn (by rw [Nat.even_add_one]; exact not_not.2 h)
      · exact h
    exact (det_even_of_odd hm (hH.submatrix _)).mul_left _

/-- **For even $n$, $|\det H|$ is a level** ($W = \pm\operatorname{adj} H$, whose diagonal is even by
`adjugate_diag_even`). -/
theorem isLevel_natAbs_det (Q : QuadForm ℤ n) (hn : Even n) : IsLevel Q Q.hessian.det.natAbs := by
  refine ⟨Q.hessian.det.sign • adjugate Q.hessian, ?_, ?_, fun i => ?_⟩
  · rw [Matrix.mul_smul, mul_adjugate, smul_smul, ← Int.sign_mul_self]
  · rw [transpose_smul, adjugate_symm (hessian_isEvenSymm Q).1]
  · rw [Matrix.smul_apply, smul_eq_mul]; exact (adjugate_diag_even hn (hessian_isEvenSymm Q) i).mul_left _

/-- A nondegenerate form has a positive level. -/
theorem exists_isLevel {Q : QuadForm ℤ n} (hQ : Q.Nondegenerate) : ∃ N, 0 < N ∧ IsLevel Q N :=
  ⟨_, by have := Int.natAbs_pos.2 hQ; omega, isLevel_two_mul_natAbs_det Q⟩

open Classical in
/-- **The level** $N = N_Q$ of an integral form (Hanke 2004, p. 355): the least $N \ge 1$ such that $NH^{-1}$ is an
even symmetric integral matrix (`IsLevel`); every level is a multiple of it (`isLevel_iff_level_dvd`). Set to $0$
for degenerate $Q$ (junk value; all theorems assume $\det H \ne 0$). Examples: $N = 1$ for $E_8$, $N = 4$ for
$x_0^2 + \dots + x_{n-1}^2$ (`level_e8`, `level_sumSq`). -/
@[kb "hanke2004" "p. 355 (level N_Q)"]
noncomputable def level (Q : QuadForm ℤ n) : ℕ :=
  if h : ∃ N, 0 < N ∧ IsLevel Q N then Nat.find h else 0

theorem level_pos {Q : QuadForm ℤ n} (hQ : Q.Nondegenerate) : 0 < level Q := by
  classical
  simp only [level, exists_isLevel hQ, ↓reduceDIte]; exact (Nat.find_spec (exists_isLevel hQ)).1

theorem isLevel_level {Q : QuadForm ℤ n} (hQ : Q.Nondegenerate) : IsLevel Q (level Q) := by
  classical
  simp only [level, exists_isLevel hQ, ↓reduceDIte]; exact (Nat.find_spec (exists_isLevel hQ)).2

theorem level_le {Q : QuadForm ℤ n} (hQ : Q.Nondegenerate) {N : ℕ} (hN : 0 < N) (h : IsLevel Q N) :
    level Q ≤ N := by
  classical
  simp only [level, exists_isLevel hQ, ↓reduceDIte]; exact Nat.find_min' _ ⟨hN, h⟩

/-- **The levels are exactly the multiples of `level Q`** (they form an ideal of $\mathbb{Z}$; Hanke's "largest
integral ideal"). -/
theorem isLevel_iff_level_dvd {Q : QuadForm ℤ n} (hQ : Q.Nondegenerate) {N : ℕ} :
    IsLevel Q N ↔ level Q ∣ N := by
  constructor
  · intro h
    have hm := h.mod (isLevel_level hQ)
    by_contra hnd
    have hpos : 0 < N % level Q := Nat.pos_of_ne_zero (fun h0 => hnd (Nat.dvd_of_mod_eq_zero h0))
    have := level_le hQ hpos hm
    have := Nat.mod_lt N (level_pos hQ)
    omega
  · rintro ⟨c, rfl⟩
    rw [mul_comm]; exact (isLevel_level hQ).mul c

/-- **$N \mid 2\det H$**. -/
theorem level_dvd_two_mul_det {Q : QuadForm ℤ n} (hQ : Q.Nondegenerate) :
    level Q ∣ 2 * Q.hessian.det.natAbs :=
  (isLevel_iff_level_dvd hQ).1 (isLevel_two_mul_natAbs_det Q)

/-- **For even $n$, $N \mid \det H$.** (For odd $n$ this fails: $n = 1$, $H = (2)$ has $N = 4$.) -/
theorem level_dvd_det {Q : QuadForm ℤ n} (hQ : Q.Nondegenerate) (hn : Even n) :
    level Q ∣ Q.hessian.det.natAbs :=
  (isLevel_iff_level_dvd hQ).1 (isLevel_natAbs_det Q hn)

/-- $\det H \cdot \det W = N^n$ when $HW = NI$. -/
theorem hessian_det_mul_det {Q : QuadForm ℤ n} {N : ℕ} {W : Matrix (Fin n) (Fin n) ℤ}
    (hW : Q.hessian * W = (N : ℤ) • 1) : Q.hessian.det * W.det = (N : ℤ) ^ n := by
  rw [← Matrix.det_mul, hW, det_smul, det_one, mul_one, Fintype.card_fin]

/-- **$\det H \mid N^n$** for every level $N$, in particular for `level Q`. -/
theorem det_dvd_pow_of_isLevel {Q : QuadForm ℤ n} {N : ℕ} (h : IsLevel Q N) :
    Q.hessian.det ∣ (N : ℤ) ^ n := by
  obtain ⟨W, hW, -⟩ := h
  exact ⟨W.det, (hessian_det_mul_det hW).symm⟩

theorem det_dvd_level_pow {Q : QuadForm ℤ n} (hQ : Q.Nondegenerate) :
    Q.hessian.det ∣ (level Q : ℤ) ^ n :=
  det_dvd_pow_of_isLevel (isLevel_level hQ)

/-- **For odd $n$, $\det H$ is even** (`det_even_of_odd`). -/
theorem hessian_det_even {Q : QuadForm ℤ n} (hn : Odd n) : Even Q.hessian.det :=
  det_even_of_odd hn (hessian_isEvenSymm Q)

/-- **Hanke 2004, Lemma 2.2 over $\mathbb{Q}$ (the $N$, $D$ part):** a prime $p$ divides the level iff it divides
$\det H$ ($= \det(2Q)$ in Hanke's notation, his $D_{2Q}$). -/
@[kb "hanke2004" "Lemma 2.2, p. 356"]
theorem prime_dvd_level_iff {Q : QuadForm ℤ n} (hQ : Q.Nondegenerate) {p : ℕ} (hp : p.Prime) :
    p ∣ level Q ↔ (p : ℤ) ∣ Q.hessian.det := by
  constructor
  · intro h
    rcases Nat.even_or_odd n with hn | hn
    · exact Int.natCast_dvd.2 (h.trans (level_dvd_det hQ hn))
    · have h2 : p ∣ 2 * Q.hessian.det.natAbs := h.trans (level_dvd_two_mul_det hQ)
      rcases (Nat.Prime.dvd_mul hp).1 h2 with h2 | h2
      · have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2
        subst hp2; exact even_iff_two_dvd.1 (hessian_det_even hn)
      · exact Int.natCast_dvd.2 h2
  · intro h
    have := h.trans (det_dvd_level_pow hQ)
    exact Int.natCast_dvd_natCast.1 (Int.Prime.dvd_pow' hp this)

/-! ### Odd $n$: $4 \mid N$ -/

/-- **For odd $n$, every level is divisible by 4.** *Proof:* $\det H$ is even
(`hessian_det_even`) and $\det H \det W = N^n$, so $N$ is even. If $N = 2u$ with $u$ odd, the even symmetric matrix
$K = \begin{pmatrix} H & uI \\ uI & W \end{pmatrix}$ of size $2n$ has $\det K = (N - u^2)^n$ (from
$K\begin{pmatrix} W & 0 \\ -uI & I\end{pmatrix} = \begin{pmatrix} (N - u^2)I & uI \\ 0 & W\end{pmatrix}$), so
$(-1)^n \det K = (u^2 - 2u)^n \equiv 3 \pmod 4$, contradicting `det_mod_four`. -/
theorem four_dvd_of_isLevel {Q : QuadForm ℤ n} (hn : Odd n) {N : ℕ} (hN : IsLevel Q N) : 4 ∣ N := by
  obtain ⟨W, hW, hWe⟩ := hN
  have hdm := hessian_det_mul_det hW
  -- $N$ is even
  have hNe : Even N := by
    have : Even ((N : ℤ) ^ n) := by rw [← hdm]; exact (hessian_det_even hn).mul_right _
    exact Int.even_coe_nat N |>.1 ((Int.even_pow.1 this).1)
  obtain ⟨u, rfl⟩ := hNe
  rcases Nat.even_or_odd u with hu | hu
  · obtain ⟨v, rfl⟩ := hu; exact ⟨v, by ring⟩
  exfalso
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd hn (by decide)
  have hWdet : W.det ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hdm
    have : ((u + u : ℕ) : ℤ) ≠ 0 := by have := hu.pos; omega
    exact (pow_ne_zero n this) hdm.symm
  let K : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ :=
    fromBlocks Q.hessian ((u : ℤ) • 1) ((u : ℤ) • 1) W
  have hK : IsEvenSymm K := by
    refine ⟨?_, fun i => ?_⟩
    · rw [fromBlocks_transpose, (hessian_isEvenSymm Q).1, hWe.1, transpose_smul, transpose_one]
    · rcases i with i | i
      · exact (hessian_isEvenSymm Q).2 i
      · exact hWe.2 i
  have hdetK : K.det = ((u + u : ℕ) - (u : ℤ) ^ 2) ^ n := by
    have hmul : K * fromBlocks W 0 (-((u : ℤ) • 1)) 1 =
        fromBlocks ((((u + u : ℕ) : ℤ) - (u : ℤ) ^ 2) • (1 : Matrix (Fin n) (Fin n) ℤ)) ((u : ℤ) • 1) 0 W := by
      simp only [K, fromBlocks_multiply, hW, Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg,
        Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, zero_add]
      congr 1
      · rw [sub_smul, sub_eq_add_neg, sq]
      · rw [add_neg_cancel]
    have := congrArg det hmul
    rw [Matrix.det_mul, det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁, det_one, mul_one, det_smul, det_one,
      mul_one, Fintype.card_fin] at this
    exact mul_right_cancel₀ hWdet this
  let e : Fin n ⊕ Fin n ≃ Fin (n + n) := finSumFinEquiv
  have h4 := det_mod_four (n := n + n) ⟨n, rfl⟩ (hK.submatrix e.symm)
  rw [det_submatrix_equiv_self e.symm K, hdetK, show (n + n) / 2 = n by omega, ← mul_pow] at h4
  obtain ⟨t, ht⟩ := hu
  obtain ⟨m, hm⟩ := hn
  have : ((-1 : ℤ) * (((u + u : ℕ) : ℤ) - (u : ℤ) ^ 2)) = 4 * (t * t - 1) + 3 := by
    rw [ht]; push_cast; ring
  rw [this, hm] at h4
  unfold IsSqMod4 at h4
  push_cast at h4
  rw [show (4 : ZMod 4) = 0 from rfl, zero_mul, zero_add, pow_succ, pow_mul,
    show (3 : ZMod 4) ^ 2 = 1 from rfl, one_pow, one_mul] at h4
  revert h4; decide

/-- **For odd $n$, $4 \mid N$** (`four_dvd_of_isLevel`). -/
@[kb "hanke2004" "p. 357 ('N is already even' for odd n; 4 | N [unverified: Shimura 1973])"]
theorem four_dvd_level {Q : QuadForm ℤ n} (hQ : Q.Nondegenerate) (hn : Odd n) : 4 ∣ level Q :=
  four_dvd_of_isLevel hn (isLevel_level hQ)

/-! ### Class invariance -/

/-- **Levels are $\mathrm{GL}_n(\mathbb{Z})$-invariant:** if $Q \sim_{\mathbb{Z}} Q'$ (`IntEquiv`, $H' = g^{\mathsf T}Hg$) and $N$ is a
level of $Q$ with $HW = NI$, then $W' = g^{-1}W g^{-\mathsf T}$ has $H'W' = NI$ and is even symmetric (`IsEvenSymm.conj`). -/
theorem IsLevel.of_intEquiv {Q Q' : QuadForm ℤ n} (h : IntEquiv Q Q') {N : ℕ} (hN : IsLevel Q N) :
    IsLevel Q' N := by
  obtain ⟨g, hg⟩ := h
  have hH : g.valᵀ * Q.hessian * g.val = Q'.hessian := (eval_mulVec_eq_iff_hessian Q Q' g.val).1 hg
  obtain ⟨W, hW, hWe⟩ := hN
  refine ⟨(g⁻¹).val * W * (g⁻¹).valᵀ, ?_, hWe.conj _⟩
  have hgg : g.val * (g⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hgg' : (g⁻¹).valᵀ * g.valᵀ = 1 := by rw [← transpose_mul, hgg, transpose_one]
  rw [← hH]
  calc g.valᵀ * Q.hessian * g.val * ((g⁻¹).val * W * (g⁻¹).valᵀ)
      = g.valᵀ * (Q.hessian * W) * (g⁻¹).valᵀ := by
        simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc g.val, hgg, Matrix.one_mul]
    _ = (N : ℤ) • 1 := by
        rw [hW, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← transpose_mul,
          show (g⁻¹).val * g.val = 1 by rw [← Units.val_mul, inv_mul_cancel, Units.val_one], transpose_one]

/-- **The level is a class invariant** ($\mathrm{GL}_n(\mathbb{Z})$-classes, `IntEquiv`). -/
@[kb "hanke2004" "p. 355 (level N_Q)"]
theorem level_eq_of_intEquiv {Q Q' : QuadForm ℤ n} (h : IntEquiv Q Q') : level Q = level Q' := by
  have hiff : ∀ N, IsLevel Q N ↔ IsLevel Q' N := fun N =>
    ⟨fun hN => hN.of_intEquiv h, fun hN => hN.of_intEquiv (IsometricGL.symm h)⟩
  have hP : IsLevel Q = IsLevel Q' := funext fun N => propext (hiff N)
  unfold level; rw [hP]

/-! ### Agreement with `IsThetaLevel` -/

private lemma det_map_real (Q : QuadForm ℤ n) :
    (Q.hessian.map (algebraMap ℤ ℝ)).det = (Q.hessian.det : ℝ) := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl

/-- $H \cdot \mathrm{dualGram}(Q) = \tfrac12 I$ over $\mathbb{R}$ (`dualGram` $= \tfrac12 H^{-1}$). -/
theorem hessian_mul_dualGram {Q : QuadForm ℤ n} (hQ : Q.Nondegenerate) :
    Q.hessian.map (algebraMap ℤ ℝ) * dualGram Q = (1 / 2 : ℝ) • 1 := by
  have hHr : Q.hessian.map (algebraMap ℤ ℝ) = (2 : ℝ) • gramMatrix Q := by
    rw [gramMatrix, smul_smul]; norm_num
  have hdet : IsUnit (gramMatrix Q).det := by
    rw [gramMatrix, det_smul, isUnit_iff_ne_zero, det_map_real]
    exact mul_ne_zero (by norm_num) (by exact_mod_cast hQ)
  rw [dualGram, Matrix.mul_smul, hHr, Matrix.smul_mul, mul_nonsing_inv _ hdet, smul_smul]; norm_num

private lemma map_natSmul_one (N : ℕ) :
    ((N : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)).map (algebraMap ℤ ℝ) = (N : ℝ) • 1 := by
  ext i j
  rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

private lemma quadAt_smul (c : ℝ) (S : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℤ) :
    quadAt (c • S) y = c * quadAt S y := by
  simp [quadAt, smul_mulVec, dotProduct_smul]

private lemma quadAt_map (W : Matrix (Fin n) (Fin n) ℤ) (y : Fin n → ℤ) :
    quadAt (W.map (algebraMap ℤ ℝ)) y = ((y ⬝ᵥ W *ᵥ y : ℤ) : ℝ) := by
  simp [quadAt, dotProduct, mulVec, Finset.mul_sum]

private lemma quadAt_single (S : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    quadAt S (Pi.single i 1) = S i i := by
  have : (fun k => ((Pi.single i (1 : ℤ) : Fin n → ℤ) k : ℝ)) = Pi.single i 1 := by
    ext k; by_cases h : k = i <;> simp [h]
  rw [quadAt, this]; simp

private lemma quadAt_single_add (S : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    quadAt S (Pi.single i 1 + Pi.single j 1) = S i i + S j j + S i j + S j i := by
  have : (fun k => (((Pi.single i (1 : ℤ) + Pi.single j 1 : Fin n → ℤ)) k : ℝ)) =
      Pi.single i 1 + Pi.single j 1 := by
    ext k; by_cases h : k = i <;> by_cases h' : k = j <;> simp [Pi.single_apply, h, h']
  rw [quadAt, this]
  simp [mulVec_add, add_dotProduct, dotProduct_add, mulVec_single]
  ring

/-- **`IsLevel` agrees with the repo's `IsThetaLevel`** ($N Q^*$ integral-valued, `Siegel/ThetaModular.lean`), for
nondegenerate $Q$ and every $N$: $NQ^*(\vec{y}) = \tfrac12\vec{y}^{\mathsf T}(NH^{-1})\vec{y}$, and a rational symmetric matrix
$M$ has $\tfrac12\vec{y}^{\mathsf T}M\vec{y} \in \mathbb{Z}$ for all $\vec{y} \in \mathbb{Z}^n$ iff $M$ is integral with even diagonal
(test $\vec{y} = e_i$ and $e_i + e_j$). -/
@[kb "hanke2004" "p. 355 (level N_Q)"]
theorem isLevel_iff_isThetaLevel {Q : QuadForm ℤ n} (hQ : Q.Nondegenerate) {N : ℕ} :
    IsLevel Q N ↔ IsThetaLevel Q N := by
  set Hr := Q.hessian.map (algebraMap ℤ ℝ) with hHr
  have hHu : IsUnit Hr.det := by rw [hHr, det_map_real, isUnit_iff_ne_zero]; exact_mod_cast hQ
  have hHD := hessian_mul_dualGram hQ
  constructor
  · rintro ⟨W, hW, hWe⟩
    have e1 : Hr * ((N : ℝ) • dualGram Q) = Hr * ((1 / 2 : ℝ) • W.map (algebraMap ℤ ℝ)) := by
      rw [Matrix.mul_smul, hHD, smul_smul, Matrix.mul_smul, hHr, ← Matrix.map_mul, hW, map_natSmul_one,
        smul_smul, mul_comm]
    have hS : (N : ℝ) • dualGram Q = (1 / 2 : ℝ) • W.map (algebraMap ℤ ℝ) := by
      rw [← nonsing_inv_mul_cancel_left Hr ((N : ℝ) • dualGram Q) hHu, e1, nonsing_inv_mul_cancel_left _ _ hHu]
    intro y
    obtain ⟨V, hV⟩ := hWe.exists_eq_add_transpose
    refine ⟨y ⬝ᵥ V *ᵥ y, ?_⟩
    rw [← quadAt_smul, hS, quadAt_smul, quadAt_map, hV, add_mulVec, dotProduct_add, mulVec_transpose,
      dotProduct_comm y (y ᵥ* V), ← dotProduct_mulVec]
    push_cast; ring
  · intro hT
    set S := (N : ℝ) • dualGram Q with hSdef
    have hSsym : Sᵀ = S := by
      have hG : (gramMatrix Q)ᵀ = gramMatrix Q := by
        have := gramMatrix_isHermitian Q
        rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
      rw [hSdef, dualGram, transpose_smul, transpose_smul, transpose_nonsing_inv, hG]
    have hT' : ∀ y : Fin n → ℤ, ∃ m : ℤ, quadAt S y = m := fun y => by
      obtain ⟨m, hm⟩ := hT y; exact ⟨m, by rw [hSdef, quadAt_smul, hm]⟩
    have hz : ∀ i j, ∃ z : ℤ, 2 * S i j = z := by
      intro i j
      by_cases hij : i = j
      · subst hij; obtain ⟨m, hm⟩ := hT' (Pi.single i 1)
        exact ⟨2 * m, by rw [← quadAt_single S i, hm]; push_cast; ring⟩
      · obtain ⟨m, hm⟩ := hT' (Pi.single i 1 + Pi.single j 1)
        obtain ⟨a, ha⟩ := hT' (Pi.single i 1)
        obtain ⟨b, hb⟩ := hT' (Pi.single j 1)
        rw [quadAt_single_add S i j] at hm
        rw [quadAt_single] at ha hb
        have hji : S j i = S i j := congrFun (congrFun hSsym i) j
        exact ⟨m - a - b, by push_cast; rw [← hm, ← ha, ← hb, hji]; ring⟩
    let W : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => (hz i j).choose
    have hWr : W.map (algebraMap ℤ ℝ) = (2 : ℝ) • S := by
      ext i j; simp only [Matrix.map_apply, of_apply, W, Matrix.smul_apply, smul_eq_mul]
      exact (hz i j).choose_spec.symm
    refine ⟨W, ?_, ?_, fun i => ?_⟩
    · apply Matrix.map_injective (f := algebraMap ℤ ℝ) (RingHom.injective_int _)
      show (Q.hessian * W).map (algebraMap ℤ ℝ) = ((N : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)).map _
      rw [Matrix.map_mul, hWr, map_natSmul_one, ← hHr, Matrix.mul_smul, hSdef, Matrix.mul_smul, hHD,
        smul_smul, smul_smul, show (2 : ℝ) * N * (1 / 2) = N by ring]
    · ext i j
      apply RingHom.injective_int (algebraMap ℤ ℝ)
      have h1 := congrFun (congrFun hWr j) i
      have h2 := congrFun (congrFun hWr i) j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at h1 h2
      rw [transpose_apply, h1, h2, ← congrFun (congrFun hSsym i) j, transpose_apply]
    · obtain ⟨m, hm⟩ := hT' (Pi.single i 1)
      rw [quadAt_single] at hm
      refine ⟨m, RingHom.injective_int (algebraMap ℤ ℝ) ?_⟩
      have h1 := congrFun (congrFun hWr i) i
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at h1
      rw [h1, hm]; simp only [algebraMap_int_eq, eq_intCast]; push_cast; ring

/-! ### Discriminant and character -/

/-- **The discriminant** $\Delta = (-1)^{\lfloor n/2 \rfloor}\det H$ of an integral form. For even $n = 2k$ this is
$(-1)^k\det H$, and $\Delta \equiv 0, 1 \pmod 4$ (`disc_mod_four`). It differs from Hanke's $(-1)^{n/2}D$
($D = \det(H/2)$, p. 357) by the square factor $2^n$, so the two give the same character at odd primes.
For odd $n$ the definition is only a convention: the theta character there is not $\left(\frac{\Delta}{\cdot}\right)$
(Shimura; Hanke p. 357 uses $(-1)^{(n-1)/2}D\,u$) and is not formalized here. -/
@[kb "hanke2004" "p. 357 (the character for even n)"]
def disc (Q : QuadForm ℤ n) : ℤ := (-1) ^ (n / 2) * Q.hessian.det

/-- For even $n$: $\Delta \equiv 0$ or $1 \pmod 4$. -/
theorem disc_mod_four (Q : QuadForm ℤ n) (hn : Even n) : IsSqMod4 (disc Q) :=
  det_mod_four hn (hessian_isEvenSymm Q)

/-- **The Jacobi symbol $\left(\frac{a}{b}\right)$ (odd $b > 0$) is periodic modulo $4M$** whenever every prime dividing
$a$ divides $M$. *Proof:* multiplicativity in $a$ reduces to $a = -1$ (period 4, `jacobiSym.at_neg_one`) and to $a = p$
prime with $p \mid M$, where $\left(\frac{p}{b}\right)$ depends on $b \bmod 4p$ (`jacobiSym.mod_right`). -/
theorem jacobiSym_eq_of_modEq {a : ℤ} {M : ℕ} (ha : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ a → p ∣ M)
    {b b' : ℕ} (hb : Odd b) (hb' : Odd b') (h : b ≡ b' [MOD 4 * M]) :
    jacobiSym a b = jacobiSym a b' := by
  -- the natural-number case
  have hnat : ∀ m : ℕ, (∀ p : ℕ, p.Prime → p ∣ m → p ∣ M) → jacobiSym m b = jacobiSym m b' := by
    intro m
    induction m using Nat.recOnMul with
    | zero =>
      intro hm
      obtain ⟨p, hpM, hp⟩ := Nat.exists_infinite_primes (M + 1)
      have hM : M = 0 := Nat.eq_zero_of_dvd_of_lt (hm p hp (dvd_zero p)) (by omega)
      rw [hM, mul_zero, Nat.modEq_zero_iff] at h
      rw [h]
    | one => intro _; simp [jacobiSym.one_left]
    | prime p hp =>
      intro hm
      have hpM := hm p hp dvd_rfl
      rw [jacobiSym.mod_right _ hb, jacobiSym.mod_right _ hb']
      have : b % (4 * p) = b' % (4 * p) := Nat.ModEq.of_dvd (mul_dvd_mul_left 4 hpM) h
      simp only [Int.natAbs_natCast]; rw [this]
    | mul x y hx hy =>
      intro hm
      push_cast
      rw [jacobiSym.mul_left, jacobiSym.mul_left,
        hx fun p hp hpx => hm p hp (hpx.mul_right y), hy fun p hp hpy => hm p hp (hpy.mul_left x)]
  have hnA : ∀ p : ℕ, p.Prime → p ∣ a.natAbs → p ∣ M := fun p hp hpa =>
    ha p hp (Int.natCast_dvd.2 hpa)
  rcases Int.natAbs_eq a with ha' | ha'
  · rw [ha']; exact hnat _ hnA
  · rw [ha', jacobiSym.neg _ hb, jacobiSym.neg _ hb', hnat _ hnA]
    congr 1
    have h4 : b ≡ b' [MOD 4] := Nat.ModEq.of_mul_right M h
    rw [(ZMod.natCast_eq_natCast_iff b b' 4).2 h4]

/-- **The quadratic character of $Q$:** $\chi_Q(b) = \left(\frac{\Delta}{b}\right)$ (Jacobi symbol, meaningful for odd
$b > 0$), $\Delta$ = `disc Q`. For even $n$ this is Hanke's $\chi_n$ (p. 357) at odd primes $b = p \nmid N$. The
Kronecker extension to even $b$ (needed when $N$ is odd) is not defined here; see `chiCharLevel_natCast_eq_kroneckerSym`.
The canonical character (positive definite, even $n$) is `chiCharLevel`; `chiCharLevel_natCast_of_odd` says it equals
`chi` at odd $b$. -/
@[kb "hanke2004" "p. 357 (the character for even n)"]
def chi (Q : QuadForm ℤ n) (b : ℕ) : ℤ := jacobiSym (disc Q) b

/-- **$\chi_Q$ is periodic modulo $4N$** on odd $b$ (item 3; proved). Every prime dividing $\Delta = \pm\det H$
divides $N$ (`prime_dvd_level_iff`), so `jacobiSym_eq_of_modEq` applies. Periodicity modulo $N$ itself (the
classical statement: $\chi_Q$ is a character mod $N$) is not proved here for nondegenerate $Q$ (it needs 2-adic
information) [unverified]; for **positive definite** $Q$ of even rank it is `chi_eq_of_modEq_level` (`ThetaCharacter.lean`,
via the theta transformation law). -/
@[kb "hanke2004" "p. 357 (the character for even n; here periodic mod 4N)"]
theorem chi_eq_of_modEq {Q : QuadForm ℤ n} (hQ : Q.Nondegenerate) {b b' : ℕ} (hb : Odd b) (hb' : Odd b')
    (h : b ≡ b' [MOD 4 * level Q]) : chi Q b = chi Q b' := by
  refine jacobiSym_eq_of_modEq (fun p hp hpd => ?_) hb hb' h
  rw [prime_dvd_level_iff hQ hp]
  unfold disc at hpd
  rcases neg_one_pow_eq_or ℤ (n / 2) with h1 | h1 <;> rw [h1] at hpd
  · simpa using hpd
  · simpa using hpd

/-- A unit of `ZMod M` with $2 \mid M$ has odd value. -/
private lemma odd_val_of_isUnit {M : ℕ} (h2 : 2 ∣ M) {x : ZMod M} (hx : IsUnit x) : Odd x.val := by
  obtain ⟨u, rfl⟩ := hx
  have hc := ZMod.val_coe_unit_coprime u
  rcases Nat.even_or_odd (u : ZMod M).val with he | ho
  · exfalso
    have : 2 ∣ Nat.gcd (u : ZMod M).val M := Nat.dvd_gcd (even_iff_two_dvd.1 he) h2
    rw [hc] at this; omega
  · exact ho

/-- **A Dirichlet character from a Jacobi symbol:** if $4 \mid M$ and $b \mapsto \left(\frac{a}{b}\right)$ is periodic
modulo $M$ on odd $b$, then $x \mapsto \left(\frac{a}{x}\right)$ ($x$ a unit, represented by its least nonnegative
residue, which is odd) is a Dirichlet character modulo $M$. -/
noncomputable def jacobiChar (a : ℤ) (M : ℕ) (h4 : 4 ∣ M) (hM : M ≠ 0)
    (hper : ∀ b b' : ℕ, Odd b → Odd b' → b ≡ b' [MOD M] → jacobiSym a b = jacobiSym a b') :
    DirichletCharacter ℤ M where
  toFun x := by classical exact if IsUnit x then jacobiSym a x.val else 0
  map_one' := by
    have : Fact (1 < M) := ⟨by obtain ⟨c, rfl⟩ := h4; omega⟩
    simp [ZMod.val_one, jacobiSym.one_right]
  map_mul' x y := by
    classical
    have h2 : 2 ∣ M := (by norm_num : 2 ∣ 4).trans h4
    by_cases hx : IsUnit x
    · by_cases hy : IsUnit y
      · simp only [hx, hy, hx.mul hy, ite_true]
        have hxo := odd_val_of_isUnit h2 hx
        have hyo := odd_val_of_isUnit h2 hy
        rw [← jacobiSym.mul_right' a (Nat.pos_of_ne_zero (by rintro h; simp [h] at hxo)).ne'
          (Nat.pos_of_ne_zero (by rintro h; simp [h] at hyo)).ne']
        apply hper _ _ (odd_val_of_isUnit h2 (hx.mul hy)) (hxo.mul hyo)
        rw [ZMod.val_mul]; exact Nat.mod_modEq _ _
      · simp [hy, hx, IsUnit.mul_iff]
    · simp [hx, IsUnit.mul_iff]
  map_nonunit' x hx := by classical simp [hx]

theorem jacobiChar_apply {a : ℤ} {M : ℕ} {h4 : 4 ∣ M} {hM : M ≠ 0} {hper} {x : ZMod M} (hx : IsUnit x) :
    jacobiChar a M h4 hM hper x = jacobiSym a x.val := by
  classical
  show (if IsUnit x then jacobiSym a x.val else 0) = _
  simp [hx]

/-- **The character of $Q$ as a Dirichlet character modulo $4N$** (values in $\mathbb{Z}$; compose with
`Int.castRingHom ℂ` via `MulChar.ringHomComp` for complex values): $\chi_Q(x) = \left(\frac{\Delta}{x}\right)$ on units
(`chiChar_apply`). For positive definite $Q$ of even rank it is induced from the canonical character `chiCharLevel`
modulo $N$ (`changeLevel_chiCharLevel`). -/
noncomputable def chiChar {Q : QuadForm ℤ n} (hQ : Q.Nondegenerate) : DirichletCharacter ℤ (4 * level Q) :=
  jacobiChar (disc Q) (4 * level Q) (dvd_mul_right 4 _) (by have := level_pos hQ; omega)
    (fun _ _ hb hb' h => chi_eq_of_modEq hQ hb hb' h)

theorem chiChar_apply {Q : QuadForm ℤ n} (hQ : Q.Nondegenerate) {x : ZMod (4 * level Q)} (hx : IsUnit x) :
    chiChar hQ x = chi Q x.val :=
  jacobiChar_apply hx

/-! ### Sanity checks (stage E) -/

/-- **A level computed from all levels:** if the levels of $Q$ are exactly the multiples of $L$, then $N_Q = L$. -/
theorem level_eq_of_forall {Q : QuadForm ℤ n} (hQ : Q.Nondegenerate) {L : ℕ}
    (h : ∀ N, IsLevel Q N ↔ L ∣ N) : level Q = L :=
  Nat.dvd_antisymm ((isLevel_iff_level_dvd hQ).1 ((h L).2 dvd_rfl))
    ((h _).1 (isLevel_level hQ))

theorem hessian_diag (a : Fin n → ℤ) : (QuadForm.diag a).hessian = diagonal fun i => 2 * a i := by
  rw [QuadForm.hessian, QuadForm.diag, diagonal_transpose, diagonal_add]
  congr 1; funext i; ring

theorem nondegenerate_diag {a : Fin n → ℤ} (ha : ∀ i, a i ≠ 0) : (QuadForm.diag a).Nondegenerate := by
  show (QuadForm.diag a).hessian.det ≠ 0
  rw [hessian_diag, det_diagonal]
  exact Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero two_ne_zero (ha i)

/-- **Levels of a diagonal form** $\langle a_0, \dots, a_{n-1}\rangle$ ($a_i \ne 0$): $N$ is a level iff $4a_i \mid N$ for
every $i$ (so $N_Q = \operatorname{lcm}_i 4|a_i|$). -/
theorem isLevel_diag_iff {a : Fin n → ℤ} (ha : ∀ i, a i ≠ 0) {N : ℕ} :
    IsLevel (QuadForm.diag a) N ↔ ∀ i, 4 * a i ∣ N := by
  constructor
  · rintro ⟨W, hW, hWe⟩ i
    have h := congrFun (congrFun hW i) i
    rw [hessian_diag, diagonal_mul, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one] at h
    obtain ⟨c, hc⟩ := hWe.2 i
    exact ⟨c, by rw [← h, hc]; ring⟩
  · intro h
    refine ⟨diagonal fun i => (N : ℤ) / (2 * a i), ?_, ?_, fun i => ?_⟩
    · rw [hessian_diag, diagonal_mul_diagonal]
      ext i j
      by_cases hij : i = j
      · subst hij
        rw [diagonal_apply_eq, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one]
        exact Int.mul_ediv_cancel' ((Dvd.intro 2 (by ring)).trans (h i))
      · rw [diagonal_apply_ne _ hij, Matrix.smul_apply, one_apply_ne hij, smul_zero]
    · exact diagonal_transpose _
    · obtain ⟨c, hc⟩ := h i
      refine ⟨c, ?_⟩
      rw [diagonal_apply_eq, hc, show 4 * a i * c = 2 * a i * (2 * c) by ring,
        Int.mul_ediv_cancel_left _ (mul_ne_zero two_ne_zero (ha i))]
      ring

/-- **$N(I_n) = 4$** for $x_0^2 + \dots + x_{n-1}^2$, $n \ge 1$ ($I_2$, $I_3$, $I_4$). -/
theorem level_sumSq (hn : 0 < n) : level (sumSq n) = 4 := by
  refine level_eq_of_forall (nondegenerate_diag fun _ => one_ne_zero) fun N => ?_
  rw [isLevel_diag_iff fun _ => one_ne_zero]
  constructor
  · intro h; exact Int.natCast_dvd_natCast.1 (by simpa using h ⟨0, hn⟩)
  · intro h _; simpa using Int.natCast_dvd_natCast.2 h

theorem det_hessian_sumSq : (sumSq n).hessian.det = 2 ^ n := by
  rw [sumSq, hessian_diag, det_diagonal]; simp

theorem disc_sumSq_two : disc (sumSq 2) = -4 := by rw [disc, det_hessian_sumSq]; norm_num
theorem disc_sumSq_four : disc (sumSq 4) = 16 := by rw [disc, det_hessian_sumSq]; norm_num

/-- $\chi_{I_2}(b) = \chi_{-4}(b)$ (Mathlib's `ZMod.χ₄`) for odd $b$: $\theta^2 \in M_1(\Gamma_0(4), \chi_{-4})$ in the table. -/
theorem chi_sumSq_two {b : ℕ} (hb : Odd b) : chi (sumSq 2) b = ZMod.χ₄ b := by
  rw [chi, disc_sumSq_two, jacobiSym.neg _ hb, jacobiSym.at_four hb, mul_one]

/-- $\chi_{I_4}$ is trivial on odd $b$ ($\Delta = 16$ is a square). -/
theorem chi_sumSq_four {b : ℕ} (hb : Odd b) : chi (sumSq 4) b = 1 := by
  rw [chi, disc_sumSq_four, show (16 : ℤ) = 4 ^ 2 by norm_num, jacobiSym.pow_left, jacobiSym.at_four hb,
    one_pow]

/-- $E_8$: $N = 1$ (from $N \mid \det H = 1$, `level_dvd_det`). -/
theorem level_e8 : level e8 = 1 := by
  have hQ : e8.Nondegenerate := by show e8.hessian.det ≠ 0; rw [e8_det]; norm_num
  have := level_dvd_det hQ (by decide : Even 8)
  rw [e8_det] at this
  exact Nat.dvd_one.1 this

theorem disc_e8 : disc e8 = 1 := by rw [disc, e8_det]; norm_num

theorem chi_e8 (b : ℕ) : chi e8 b = 1 := by rw [chi, disc_e8, jacobiSym.one_left]

/-- $x_0^2 + x_1^2 + x_2^2 + 2x_3^2$. -/
def q1112 : QuadForm ℤ 4 := QuadForm.diag ![1, 1, 1, 2]

/-- $N = 8$ for $x_0^2 + x_1^2 + x_2^2 + 2x_3^2$. -/
theorem level_q1112 : level q1112 = 8 := by
  have ha : ∀ i, (![1, 1, 1, 2] : Fin 4 → ℤ) i ≠ 0 := by decide
  refine level_eq_of_forall (nondegenerate_diag ha) fun N => ?_
  rw [isLevel_diag_iff ha, Fin.forall_fin_succ, Fin.forall_fin_succ, Fin.forall_fin_succ,
    Fin.forall_fin_one]
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_succ]
  constructor
  · rintro ⟨-, -, -, h⟩; exact Int.natCast_dvd_natCast.1 (by simpa using h)
  · intro h
    have h8 : (8 : ℤ) ∣ N := by exact_mod_cast h
    refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num <;> first | exact h8 | exact (by norm_num : (4 : ℤ) ∣ 8).trans h8

theorem det_hessian_q1112 : q1112.hessian.det = 32 := by
  rw [q1112, hessian_diag, det_diagonal, Fin.prod_univ_four]; simp

theorem disc_q1112 : disc q1112 = 32 := by rw [disc, det_hessian_q1112]; norm_num

/-- $\chi(b) = \chi_8(b)$ (Mathlib's `ZMod.χ₈`, $= \left(\frac{2}{b}\right)$) for odd $b$, for $x_0^2+x_1^2+x_2^2+2x_3^2$. -/
theorem chi_q1112 {b : ℕ} (hb : Odd b) : chi q1112 b = ZMod.χ₈ b := by
  rw [chi, disc_q1112, show (32 : ℤ) = 2 * 4 ^ 2 by norm_num, jacobiSym.mul_left, jacobiSym.pow_left,
    jacobiSym.at_four hb, jacobiSym.at_two hb, one_pow, mul_one]

/-- $A_2 \oplus A_2$: $x_0^2 + x_0x_1 + x_1^2 + x_2^2 + x_2x_3 + x_3^2$. -/
def a2a2 : QuadForm ℤ 4 := QuadForm.ofUpper ![![1, 1, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 1], ![0, 0, 0, 1]]

theorem a2a2_hessian : a2a2.hessian = !![2, 1, 0, 0; 1, 2, 0, 0; 0, 0, 2, 1; 0, 0, 1, 2] := by decide

theorem det_hessian_a2a2 : a2a2.hessian.det = 9 := by
  rw [a2a2_hessian, det_succ_row_zero]
  simp [Fin.sum_univ_succ, det_fin_three, Fin.succAbove]

theorem disc_a2a2 : disc a2a2 = 9 := by rw [disc, det_hessian_a2a2]; norm_num

/-- $N = 3$ for $A_2 \oplus A_2$: $3H^{-1} = \begin{pmatrix}2&-1\\-1&2\end{pmatrix}^{\oplus 2}$ is even, and $N = 1$ is impossible since
$\det H = 9 \nmid 1$. -/
theorem level_a2a2 : level a2a2 = 3 := by
  have hQ : a2a2.Nondegenerate := by show a2a2.hessian.det ≠ 0; rw [det_hessian_a2a2]; norm_num
  have h3 : IsLevel a2a2 3 := by
    refine ⟨!![2, -1, 0, 0; -1, 2, 0, 0; 0, 0, 2, -1; 0, 0, -1, 2], ?_, ?_, ?_⟩
    · rw [a2a2_hessian]; decide
    · decide
    · decide
  have hd : level a2a2 ∣ 3 := (isLevel_iff_level_dvd hQ).1 h3
  rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h1
  · exfalso
    have := det_dvd_pow_of_isLevel (h1 ▸ isLevel_level hQ)
    rw [det_hessian_a2a2] at this; norm_num at this
  · exact h1

/-- $\chi_{A_2 \oplus A_2}$ is trivial on odd $b$ prime to 3 ($\Delta = 9$ is a square). -/
theorem chi_a2a2 {b : ℕ} (hb : Nat.Coprime 3 b) : chi a2a2 b = 1 := by
  rw [chi, disc_a2a2, show (9 : ℤ) = 3 ^ 2 by norm_num]
  exact jacobiSym.sq_one' (by simpa [Int.gcd] using hb)

end QuadFormsKB.Siegel
