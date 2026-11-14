/-
# Kitaoka 1993, §5.6, Exercise (p. 99): the local density vanishes exactly when there is no isometry

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §5.6, the Exercise after Proposition 5.6.1, p. 99
(printed page): "Show $\beta_p(M, N; g, p^e) \ne 0$ if and only if there exists an isometry $\sigma$ from $M$ to $N$
such that $\sigma(x) \equiv g(x) \bmod p^eN$ for $x \in M$. In particular, $\operatorname{rank} M > \operatorname{rank} N$
implies $\beta_p(M, N; g, p^e) = 0$."

**Setting** (as in `Ch5Densities.lean`). $p$ is a prime, $S$ an integral symmetric $n \times n$ matrix (the Gram
matrix of $N$), $T$ an integral symmetric $m \times m$ matrix with $\det T \ne 0$ (the Gram matrix of the regular
lattice $M$). An isometry $M \to N$ is, through matrix representation, an $X \in M_{n,m}(\mathbb Z_p)$ with
$S[X] = X^{\mathsf T}SX = T$. Only the case $e = 0$ (no congruence condition) is treated, which is the density
$\beta_p(M, N)$ of `betaP`.

**Proves**
* `exists_isometry_of_cong`: if $S[X] \equiv T \bmod p^k$ entrywise with $p^k \nmid 4\det T$ (i.e.
  $k > \operatorname{ord}_p(4\det T)$), then $S[XV] = T$ for some $V \in \mathrm{GL}_m(\mathbb Z_p)$ (from Cassels'
  Lemma 8.5.1 in the form `QuadFormsKB.Cassels.exists_equiv_of_dvd_pow`);
* `betaP_nonneg`: $\beta_p(M, N) \ge 0$;
* `exercise_p99` (**the Exercise**, $e = 0$): $\beta_p(M, N) \ne 0$ if and only if there is an
  $X \in M_{n,m}(\mathbb Z_p)$ with $S[X] = T$;
* `betaP_pos_iff`: equivalently $\beta_p(M, N) > 0$ if and only if such an $X$ exists;
* `betaP_eq_zero_of_lt` (the "in particular"): if $m > n$ then $\beta_p(M, N) = 0$.

*Proof.* By Proposition 5.6.1 (i) (`betaP_eq`), $\beta_p(M, N) = (p^r)^{m(m+1)/2-mn}\#A_{p^r}(T, S)$ for every
$r \ge h + 1$. If $S[X_0] = T$, the residue of $X_0$ modulo $p^{h+1}$ lies in $A_{p^{h+1}}(T, S)$, so the count is
positive. Conversely, if $\beta_p \ne 0$, then $A_{p^r}(T, S) \ne \emptyset$ for $r$ large; an element $X$ satisfies
$S[X] \equiv T \bmod p^r$, and Cassels' lemma (a Hensel argument) makes $T$ and $S[X]$ equivalent: $S[X] = T[U]$, so
$S[XU^{-1}] = T$. If $m > n$, $S[X] = T$ is impossible since $\operatorname{rank} T = m$ but
$\operatorname{rank} X^{\mathsf T}SX \le n$.

The result is unconditional (no named input hypotheses).
-/
import QuadFormsKB.Literature.Kitaoka.Wave2.Ch5Stabilization
import QuadFormsKB.Literature.Cassels.Ch8.Congruent

open Matrix Filter

noncomputable section

namespace QuadFormsKB.Kitaoka.Density

variable {p : ℕ} [hp : Fact p.Prime] {m n : ℕ}

/-- **From an approximate to an exact isometry.** If $S[X] \equiv T \bmod p^k$ entrywise and
$k > \operatorname{ord}_p(4\det T)$, then $S[XV] = T$ for an invertible $V$ (Cassels' Lemma 8.5.1,
`QuadFormsKB.Cassels.exists_equiv_of_dvd_pow`, applied to $F = T$, $G = S[X]$). -/
theorem exists_isometry_of_cong {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]}
    (hS : Sᵀ = S) (hT : Tᵀ = T) (hdet : T.det ≠ 0) {k : ℕ} (hk : ((4 : ℤ_[p]) * T.det).valuation < k)
    (X : Matrix (Fin n) (Fin m) ℤ_[p]) (hX : ∀ i j, (p : ℤ_[p]) ^ k ∣ (Xᵀ * S * X - T) i j) :
    ∃ V : Matrix (Fin m) (Fin m) ℤ_[p], IsUnit V ∧ (X * V)ᵀ * S * (X * V) = T := by
  have hG : (Xᵀ * S * X)ᵀ = Xᵀ * S * X := by simp [transpose_mul, hS, Matrix.mul_assoc]
  obtain ⟨U, -, hU⟩ := Cassels.exists_equiv_of_dvd_pow T (Xᵀ * S * X) hT hG hdet k hk
    (fun i j => by
      have := hX i j
      rw [Matrix.sub_apply] at this
      rw [← neg_sub]
      exact (dvd_neg).mpr this)
  refine ⟨(U⁻¹ : GL (Fin m) ℤ_[p]).val, (U⁻¹).isUnit, ?_⟩
  have h1 : (U⁻¹ : GL (Fin m) ℤ_[p]).val * U.val = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc (X * (U⁻¹ : GL (Fin m) ℤ_[p]).val)ᵀ * S * (X * (U⁻¹ : GL (Fin m) ℤ_[p]).val)
      = ((U⁻¹ : GL (Fin m) ℤ_[p]).val)ᵀ * (Xᵀ * S * X) * (U⁻¹ : GL (Fin m) ℤ_[p]).val := by
        simp only [transpose_mul, Matrix.mul_assoc]
    _ = ((U⁻¹ : GL (Fin m) ℤ_[p]).val)ᵀ * ((U.val)ᵀ * T * U.val) * (U⁻¹ : GL (Fin m) ℤ_[p]).val := by rw [hU]
    _ = (U.val * (U⁻¹ : GL (Fin m) ℤ_[p]).val)ᵀ * T * (U.val * (U⁻¹ : GL (Fin m) ℤ_[p]).val) := by
        simp only [transpose_mul, Matrix.mul_assoc]
    _ = T := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one, transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem normA_nonneg (S : Matrix (Fin n) (Fin n) ℤ_[p]) (T : Matrix (Fin m) (Fin m) ℤ_[p]) (r : ℕ) :
    0 ≤ normA p S T r := by
  unfold normA
  have : (0 : ℝ) < (p : ℝ) ^ r := pow_pos (by exact_mod_cast hp.out.pos) r
  positivity

/-- **$\beta_p(M, N) \ge 0$** for integral symmetric $S$ and integral symmetric regular $T$. -/
theorem betaP_nonneg {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]} (hS : Sᵀ = S)
    (hT : Tᵀ = T) (hdet : T.det ≠ 0) : 0 ≤ betaP p S T := by
  obtain ⟨h, A, hA, hAE⟩ := exists_h hT hdet
  rw [betaP_eq hS hT hA hAE le_rfl]
  exact normA_nonneg S T _

/-- An exact isometry gives an element of $A_{p^r}(T, S)$ for every $r \ge 1$. -/
theorem countA_pos_of_isometry {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]}
    (hS : Sᵀ = S) (hT : Tᵀ = T) {r : ℕ} (hr : 1 ≤ r) {X : Matrix (Fin n) (Fin m) ℤ_[p]}
    (hX : Xᵀ * S * X = T) : 0 < countA p r S T := by
  classical
  rw [countA_eq_card hS hT]
  have hmem : GoodA p r r S T (X.map (red p r)) := by
    rw [GoodA, modE_gram_iff_of_mcong hS hr (mcong_liftRes_red X), hX, sub_self]
    exact ModE.zero
  have : Nonempty {Y // GoodA p r r S T Y} := ⟨⟨_, hmem⟩⟩
  exact Nat.card_pos

theorem normA_pos_iff (S : Matrix (Fin n) (Fin n) ℤ_[p]) (T : Matrix (Fin m) (Fin m) ℤ_[p]) (r : ℕ) :
    normA p S T r ≠ 0 ↔ countA p r S T ≠ 0 := by
  unfold normA
  have : ((p : ℝ) ^ r) ^ (((m * (m + 1) / 2 : ℕ) : ℤ) - (m : ℤ) * n) ≠ 0 :=
    zpow_ne_zero _ (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero))
  rw [mul_ne_zero_iff, Nat.cast_ne_zero]
  exact ⟨fun h => h.2, fun h => ⟨this, h⟩⟩

/-- **Kitaoka 1993, Exercise after Proposition 5.6.1** (p. 99), case $e = 0$: for an integral symmetric $S$
($n \times n$, the Gram matrix of $N$) and an integral symmetric $T$ ($m \times m$, the Gram matrix of $M$) with
$\det T \ne 0$, $\beta_p(M, N) \ne 0$ if and only if there exists an isometry from $M$ to $N$, i.e. an
$X \in M_{n,m}(\mathbb Z_p)$ with $X^{\mathsf T}SX = T$. -/
@[kb "kitaoka1993" "§5.6, Exercise, p. 99"]
theorem exercise_p99 {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]} (hS : Sᵀ = S)
    (hT : Tᵀ = T) (hdet : T.det ≠ 0) :
    betaP p S T ≠ 0 ↔ ∃ X : Matrix (Fin n) (Fin m) ℤ_[p], Xᵀ * S * X = T := by
  obtain ⟨h, A, hA, hAE⟩ := exists_h hT hdet
  constructor
  · intro hβ
    set k := ((4 : ℤ_[p]) * T.det).valuation + 1
    set r := max (h + 1) k
    rw [betaP_eq hS hT hA hAE (le_max_left (h + 1) k), normA_pos_iff] at hβ
    unfold countA at hβ
    obtain ⟨⟨X, hX⟩⟩ := (Nat.card_ne_zero.mp hβ).1
    obtain ⟨V, -, hV⟩ := exists_isometry_of_cong hS hT hdet (k := k) (Nat.lt_succ_self _) (liftRes p r X)
      (fun i j => dvd_trans (dvd_trans (pow_dvd_pow _ (le_max_right (h + 1) k)) (dvd_mul_right _ _)) (hX i j))
    exact ⟨_, hV⟩
  · rintro ⟨X, hX⟩
    rw [betaP_eq hS hT hA hAE le_rfl, normA_pos_iff]
    exact (countA_pos_of_isometry hS hT (by omega) hX).ne'

/-- **$\beta_p(M, N) > 0$ if and only if $M$ is represented by $N$** (equivalent form of `exercise_p99`). -/
theorem betaP_pos_iff {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]} (hS : Sᵀ = S)
    (hT : Tᵀ = T) (hdet : T.det ≠ 0) :
    0 < betaP p S T ↔ ∃ X : Matrix (Fin n) (Fin m) ℤ_[p], Xᵀ * S * X = T := by
  rw [← exercise_p99 hS hT hdet]
  exact ⟨fun h => h.ne', fun h => lt_of_le_of_ne (betaP_nonneg hS hT hdet) (Ne.symm h)⟩

/-- No isometry from a regular lattice of rank $m$ into a lattice of rank $n < m$: $X^{\mathsf T}SX = T$ with
$\det T \ne 0$ forces $m \le n$ (compare ranks over $\mathbb Q_p$). -/
theorem le_of_isometry {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]} (hdet : T.det ≠ 0)
    {X : Matrix (Fin n) (Fin m) ℤ_[p]} (hX : Xᵀ * S * X = T) : m ≤ n := by
  set φ : ℤ_[p] →+* ℚ_[p] := PadicInt.Coe.ringHom
  have hdet' : (T.map φ).det ≠ 0 := by
    rw [show (T.map φ).det = φ T.det from (RingHom.map_det φ T).symm]
    exact fun h => hdet (PadicInt.coe_eq_zero.mp h)
  have hunit : IsUnit (T.map φ) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet')
  have hrank : (T.map φ).rank = m := by
    rw [Matrix.rank_of_isUnit _ hunit, Fintype.card_fin]
  have hmul : T.map φ = (Xᵀ.map φ) * ((S.map φ) * (X.map φ)) := by
    rw [← hX, Matrix.map_mul, Matrix.map_mul, Matrix.mul_assoc]
  calc m = (T.map φ).rank := hrank.symm
    _ ≤ (Xᵀ.map φ).rank := by rw [hmul]; exact Matrix.rank_mul_le_left _ _
    _ ≤ n := Matrix.rank_le_width _

/-- **Kitaoka 1993, Exercise after Proposition 5.6.1** (p. 99), "in particular": if $\operatorname{rank} M = m$ exceeds
$\operatorname{rank} N = n$, then $\beta_p(M, N) = 0$ ($S$ integral symmetric, $T$ integral symmetric regular). -/
@[kb "kitaoka1993" "§5.6, Exercise, p. 99 (rank M > rank N)"]
theorem betaP_eq_zero_of_lt {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]} (hS : Sᵀ = S)
    (hT : Tᵀ = T) (hdet : T.det ≠ 0) (hmn : n < m) : betaP p S T = 0 := by
  by_contra hβ
  obtain ⟨X, hX⟩ := (exercise_p99 hS hT hdet).mp hβ
  exact absurd (le_of_isometry hdet hX) (not_le.mpr hmn)

end QuadFormsKB.Kitaoka.Density
