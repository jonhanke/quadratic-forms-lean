/-
# Kitaoka 1993, §5.6, p. 100: the primitive local density is a stable value, and when it is nonzero

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §5.6, p. 100 (printed page): the primitive local
density $d_p(M, N)$ is well defined, and "$d_p(M, N) = 0$ unless there exists an isometry $\sigma : M \to N$ such
that $\sigma(M)$ is primitive in $N$".

**Setting** (as in `Ch5Primitive.lean`). $p$ is a prime, $S$ an integral symmetric $n \times n$ matrix, $T$ an integral
symmetric $m \times m$ matrix. A matrix $X \in M_{n,m}(\mathbb Z_p)$ is primitive (`IsPrimMat`) when $X \bmod p$ has
rank $m$. `countPrim p r S T` counts the primitive classes in $A_{p^r}(T, S)$, and `primDensity` is the limit of the
normalized counts $(p^r)^{m(m+1)/2 - mn}\,\#\{X \in A_{p^r}(T, S) \mid X \text{ primitive}\}$.

**Proves**
* `isPrimMat_of_mcong`: primitivity depends only on $X \bmod p$;
* `isPrimMat_mul_unit`: $X U$ is primitive iff $X$ is, for $U \in \mathrm{GL}_m(\mathbb Z_p)$;
* `countPrim_succ`: $p^{nm}\,\#\mathrm{Prim}_{p^r} = p^{m(m+1)/2}\,\#\mathrm{Prim}_{p^{r+1}}$ for $r \ge h + 1$;
* `lemma561_prim`, `primDensity_eq` (**$d_p$ is well defined**): the normalized sequence is constant for
  $r \ge h + 1$, and equals $d_p(M, N)$; `tendsto_normPrim` records the convergence;
* `primDensity_le_betaP`: $0 \le d_p(M, N) \le \beta_p(M, N)$;
* `primDensity_ne_zero_iff`: $d_p(M, N) \ne 0$ if and only if there is an isometry
  $X \in M_{n,m}(\mathbb Z_p)$ with $X^{\mathsf T}SX = T$ and $X$ primitive.

*Proof.* Identical to the one for $\beta_p$ (`Ch5Stabilization.lean`) with the predicate "primitive" carried along:
in the lifting step (`card_lift`) the predicate depends on $X \bmod p^r$ only, since $X \bmod p$ is determined by it;
in the class bijection (`card_class`) $X \mapsto XV$ with $V \in \mathrm{GL}_m(\mathbb Z_p)$ preserves the rank of
$X \bmod p$. For the last statement one argues as in the Exercise (`exercise_p99`): a primitive element of
$A_{p^r}(T, S)$ for $r$ large is corrected by an invertible $V$ (`exists_isometry_of_cong`) to an exact primitive
isometry, and conversely the residue of an exact primitive isometry lies in the primitive count.

The results are unconditional (no named input hypotheses).
-/
import QuadFormsKB.Literature.Kitaoka.Wave3.Ch5Primitive
import QuadFormsKB.Literature.Kitaoka.Wave2.Ch5Stabilization
import QuadFormsKB.Literature.Kitaoka.Wave3.Ch5Exercise

open Matrix Filter

noncomputable section

namespace QuadFormsKB.Kitaoka.Density

variable {p : ℕ} [hp : Fact p.Prime] {m n : ℕ}

/-! ### Primitivity depends on the residue mod $p$, and is invariant under units -/

theorem map_toZMod_eq_of_mcong {a b k : ℕ} (hk : 1 ≤ k) {X X' : Matrix (Fin a) (Fin b) ℤ_[p]}
    (h : MCong p k X X') :
    X.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) = X'.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) := by
  obtain ⟨Y, rfl⟩ := h
  ext i j
  have hp0 : ((PadicInt.toZMod : ℤ_[p] →+* ZMod p) (p : ℤ_[p])) = 0 := by
    rw [map_natCast]; exact ZMod.natCast_self p
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_pow, hp0]
  rw [zero_pow (by omega)]
  simp

/-- **Primitivity depends only on $X \bmod p$** (so only on $X \bmod p^k$ for $k \ge 1$). -/
theorem isPrimMat_of_mcong {k : ℕ} (hk : 1 ≤ k) {X X' : Matrix (Fin n) (Fin m) ℤ_[p]}
    (h : MCong p k X X') : IsPrimMat p X ↔ IsPrimMat p X' := by
  unfold IsPrimMat
  rw [map_toZMod_eq_of_mcong hk h]

/-- **Primitivity is invariant under right multiplication by an invertible matrix.** -/
theorem isPrimMat_mul_unit {X : Matrix (Fin n) (Fin m) ℤ_[p]} {U V : Matrix (Fin m) (Fin m) ℤ_[p]}
    (hUV : U * V = 1) : IsPrimMat p (X * U) ↔ IsPrimMat p X := by
  unfold IsPrimMat
  have h1 : (U.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p)) * (V.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p)) = 1 := by
    rw [← Matrix.map_mul, hUV, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [Matrix.map_mul, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnit_det_of_right_inverse h1)]

/-! ### Counting -/

theorem countPrim_eq_card {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]} (hS : Sᵀ = S)
    (hT : Tᵀ = T) (r : ℕ) :
    countPrim p r S T = Nat.card {X // GoodA p r r S T X ∧ IsPrimMat p (liftRes p r X)} := by
  unfold countPrim
  refine Nat.card_congr (Equiv.subtypeEquivRight fun X => and_congr (modE_iff_dvd ?_).symm Iff.rfl)
  simp [transpose_sub, transpose_mul, hS, hT, Matrix.mul_assoc]

/-- **Lifting, primitive version** (Kitaoka, proof of Lemma 5.6.1, p. 94). -/
theorem card_lift_prim {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]} (hS : Sᵀ = S)
    {r : ℕ} (hr : 1 ≤ r) (a : ℕ) :
    Nat.card {X : Matrix (Fin n) (Fin m) (Fin (p ^ (r + a))) //
        GoodA p (r + a) r S T X ∧ IsPrimMat p (liftRes p (r + a) X)} =
      Nat.card {X // GoodA p r r S T X ∧ IsPrimMat p (liftRes p r X)} * (p ^ a) ^ (n * m) := by
  have hX : ∀ X : Matrix (Fin n) (Fin m) (Fin (p ^ (r + a))),
      (GoodA p (r + a) r S T X ∧ IsPrimMat p (liftRes p (r + a) X)) ↔
        (GoodA p r r S T (splitM p r a X).1 ∧ IsPrimMat p (liftRes p r (splitM p r a X).1)) := fun X =>
    and_congr (modE_gram_iff_of_mcong hS hr (mcong_splitM r a X)) (isPrimMat_of_mcong hr (mcong_splitM r a X))
  have e1 : {X : Matrix (Fin n) (Fin m) (Fin (p ^ (r + a))) //
      GoodA p (r + a) r S T X ∧ IsPrimMat p (liftRes p (r + a) X)} ≃
      {Y : Matrix (Fin n) (Fin m) (Fin (p ^ r)) × Matrix (Fin n) (Fin m) (Fin (p ^ a)) //
        GoodA p r r S T Y.1 ∧ IsPrimMat p (liftRes p r Y.1)} :=
    Equiv.subtypeEquiv (splitM p r a) hX
  have e2 : {Y : Matrix (Fin n) (Fin m) (Fin (p ^ r)) × Matrix (Fin n) (Fin m) (Fin (p ^ a)) //
      GoodA p r r S T Y.1 ∧ IsPrimMat p (liftRes p r Y.1)} ≃
      {X : Matrix (Fin n) (Fin m) (Fin (p ^ r)) // GoodA p r r S T X ∧ IsPrimMat p (liftRes p r X)} ×
        Matrix (Fin n) (Fin m) (Fin (p ^ a)) :=
    Equiv.prodSubtypeFstEquivSubtypeProd
      (p := fun X : Matrix (Fin n) (Fin m) (Fin (p ^ r)) => GoodA p r r S T X ∧ IsPrimMat p (liftRes p r X))
  have hc : Nat.card (Matrix (Fin n) (Fin m) (Fin (p ^ a))) = (p ^ a) ^ (n * m) := by
    rw [show Nat.card (Matrix (Fin n) (Fin m) (Fin (p ^ a))) = Nat.card (Fin n → Fin m → Fin (p ^ a)) from rfl,
      Nat.card_fun, Nat.card_fun]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul]; ring
  rw [Nat.card_congr (e1.trans e2), Nat.card_prod, hc]

theorem isPrimMat_red_mul {L : Matrix (Fin n) (Fin m) ℤ_[p]} {U V : Matrix (Fin m) (Fin m) ℤ_[p]}
    (hUV : U * V = 1) {k : ℕ} (hk : 1 ≤ k) :
    IsPrimMat p (liftRes p k ((L * U).map (red p k))) ↔ IsPrimMat p L :=
  (isPrimMat_of_mcong hk (mcong_liftRes_red (L * U))).trans (isPrimMat_mul_unit hUV)

/-- **The classes are equinumerous, primitive version** (Kitaoka, proof of Lemma 5.6.1, p. 95). -/
theorem card_class_prim {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]} (hS : Sᵀ = S)
    (hT : Tᵀ = T) {h : ℕ} {A : Matrix (Fin m) (Fin m) ℤ_[p]} (hA : T * A = (p : ℤ_[p]) ^ h • 1)
    (hAE : ModE p 0 A) {r : ℕ} (hr : h + 1 ≤ r) (c : Sym2 (Fin m) → Fin (p ^ 1)) :
    Nat.card {X : Matrix (Fin n) (Fin m) (Fin (p ^ (r + 1))) //
      GoodA p (r + 1) (r + 1) S (T + (p : ℤ_[p]) ^ r • (classF c + (classF c)ᵀ)) X ∧
        IsPrimMat p (liftRes p (r + 1) X)} =
    Nat.card {X // GoodA p (r + 1) (r + 1) S T X ∧ IsPrimMat p (liftRes p (r + 1) X)} := by
  obtain ⟨U, V, hUV, hVU, hU⟩ := exists_hensel hT hA hAE hr (classF c)
  set Tc := T + (p : ℤ_[p]) ^ r • (classF c + (classF c)ᵀ)
  have h1 : 1 ≤ r + 1 := by omega
  refine Nat.card_congr
    { toFun := fun X => ⟨(liftRes p (r + 1) X.1 * V).map (red p (r + 1)), ?_, ?_⟩
      invFun := fun Y => ⟨(liftRes p (r + 1) Y.1 * U).map (red p (r + 1)), ?_, ?_⟩
      left_inv := fun X => ?_
      right_inv := fun Y => ?_ }
  · rw [GoodA, modE_gram_iff_of_mcong hS h1 (mcong_liftRes_red _)]
    set L := liftRes p (r + 1) X.1
    have hI : Vᵀ * (Uᵀ * T * U) * V = T := by
      rw [show Vᵀ * (Uᵀ * T * U) * V = (U * V)ᵀ * T * (U * V) by
        simp only [transpose_mul, Matrix.mul_assoc], hUV, transpose_one, Matrix.one_mul, Matrix.mul_one]
    have key : (L * V)ᵀ * S * (L * V) - T = Vᵀ * (Lᵀ * S * L - Tc) * V - Vᵀ * (Uᵀ * T * U - Tc) * V := by
      calc (L * V)ᵀ * S * (L * V) - T = Vᵀ * (Lᵀ * S * L) * V - Vᵀ * (Uᵀ * T * U) * V := by
            rw [hI, transpose_mul]; simp only [Matrix.mul_assoc]
        _ = _ := by simp only [Matrix.mul_sub, Matrix.sub_mul]; abel
    rw [key]
    exact (X.2.1.conj V).sub (hU.conj V)
  · exact (isPrimMat_red_mul hVU h1).mpr X.2.2
  · rw [GoodA, modE_gram_iff_of_mcong hS h1 (mcong_liftRes_red _)]
    set L := liftRes p (r + 1) Y.1
    have key : (L * U)ᵀ * S * (L * U) - Tc = Uᵀ * (Lᵀ * S * L - T) * U + (Uᵀ * T * U - Tc) := by
      rw [transpose_mul]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      abel
    rw [key]
    exact (Y.2.1.conj U).add hU
  · exact (isPrimMat_red_mul hUV h1).mpr Y.2.2
  · apply Subtype.ext
    have hm : MCong p (r + 1) (liftRes p (r + 1) ((liftRes p (r + 1) X.1 * V).map (red p (r + 1))) * U)
        (liftRes p (r + 1) X.1) := by
      have := (mcong_liftRes_red (k := r + 1) (liftRes p (r + 1) X.1 * V)).mul_right U
      rwa [Matrix.mul_assoc, hVU, Matrix.mul_one] at this
    exact (red_map_eq_of_mcong hm).trans (red_map_liftRes _)
  · apply Subtype.ext
    have hm : MCong p (r + 1) (liftRes p (r + 1) ((liftRes p (r + 1) Y.1 * U).map (red p (r + 1))) * V)
        (liftRes p (r + 1) Y.1) := by
      have := (mcong_liftRes_red (k := r + 1) (liftRes p (r + 1) Y.1 * U)).mul_right V
      rwa [Matrix.mul_assoc, hUV, Matrix.mul_one] at this
    exact (red_map_eq_of_mcong hm).trans (red_map_liftRes _)

/-- **The counting identity of Lemma 5.6.1 for primitive solutions**:
$p^{nm}\#\mathrm{Prim}_{p^r}(T, S) = p^{m(m+1)/2}\#\mathrm{Prim}_{p^{r+1}}(T, S)$ for $r \ge h + 1$. -/
theorem countPrim_succ {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]} (hS : Sᵀ = S)
    (hT : Tᵀ = T) {h : ℕ} {A : Matrix (Fin m) (Fin m) ℤ_[p]} (hA : T * A = (p : ℤ_[p]) ^ h • 1)
    (hAE : ModE p 0 A) {r : ℕ} (hr : h + 1 ≤ r) :
    countPrim p r S T * p ^ (n * m) = p ^ (m * (m + 1) / 2) * countPrim p (r + 1) S T := by
  classical
  rw [countPrim_eq_card hS hT, countPrim_eq_card hS hT]
  have h1 := card_lift_prim (p := p) (T := T) hS (r := r) (by omega) 1
  rw [pow_one] at h1
  rw [← h1]
  have : Nonempty (Fin (p ^ 1)) := ⟨⟨0, pow_pos hp.out.pos 1⟩⟩
  let Fib : (Sym2 (Fin m) → Fin (p ^ 1)) → Matrix (Fin n) (Fin m) (Fin (p ^ (r + 1))) → Prop := fun c X =>
    GoodA p (r + 1) (r + 1) S (T + (p : ℤ_[p]) ^ r • (classF c + (classF c)ᵀ)) X
  let κ : Matrix (Fin n) (Fin m) (Fin (p ^ (r + 1))) → Sym2 (Fin m) → Fin (p ^ 1) := fun X =>
    Classical.epsilon fun c => Fib c X
  have hP : ∀ c X, Fib c X → GoodA p (r + 1) r S T X := by
    intro c X hX
    have := (ModE.mono hX (Nat.le_succ r)).add (⟨classF c, rfl⟩ : ModE p r ((p : ℤ_[p]) ^ r • (classF c + (classF c)ᵀ)))
    convert this using 1
    abel
  have hfib : ∀ c X, (GoodA p (r + 1) r S T X ∧ κ X = c) ↔ Fib c X := by
    intro c X
    constructor
    · rintro ⟨hX, rfl⟩
      obtain ⟨c, hc⟩ := exists_class hX
      exact Classical.epsilon_spec (p := fun c => Fib c X) ⟨c, by
        simp only [Fib, GoodA]; convert hc using 1; abel⟩
    · intro hX
      refine ⟨hP c X hX, ?_⟩
      have hκ : Fib (κ X) X := Classical.epsilon_spec (p := fun c => Fib c X) ⟨c, hX⟩
      exact class_unique (D := (liftRes p (r + 1) X)ᵀ * S * liftRes p (r + 1) X - T)
        (by simp only [Fib, GoodA] at hκ; convert hκ using 1; abel)
        (by simp only [Fib, GoodA] at hX; convert hX using 1; abel)
  have hfibQ : ∀ c X, ((GoodA p (r + 1) r S T X ∧ IsPrimMat p (liftRes p (r + 1) X)) ∧ κ X = c) ↔
      (Fib c X ∧ IsPrimMat p (liftRes p (r + 1) X)) := by
    intro c X
    rw [and_right_comm, hfib]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_eq_sum_card_fiberwise (f := κ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  have hc : ∀ c, (Finset.univ.filter (fun X => GoodA p (r + 1) r S T X ∧
        IsPrimMat p (liftRes p (r + 1) X)) |>.filter fun X => κ X = c).card =
      Nat.card {X // GoodA p (r + 1) (r + 1) S T X ∧ IsPrimMat p (liftRes p (r + 1) X)} := by
    intro c
    rw [Finset.filter_filter, ← card_class_prim hS hT hA hAE hr c, Nat.card_eq_fintype_card,
      Fintype.card_subtype]
    congr 1
    ext X
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hfibQ c X
  rw [Finset.sum_congr rfl fun c _ => hc c, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card, card_sym2_fun]

/-! ### Stabilization -/

/-- The sequence $(p^r)^{m(m+1)/2 - mn}\#\mathrm{Prim}_{p^r}(T, S)$ whose limit is $d_p(M, N)$. -/
def normPrim (p : ℕ) [Fact p.Prime] (S : Matrix (Fin n) (Fin n) ℤ_[p]) (T : Matrix (Fin m) (Fin m) ℤ_[p])
    (r : ℕ) : ℝ :=
  ((p : ℝ) ^ r) ^ (((m * (m + 1) / 2 : ℕ) : ℤ) - (m : ℤ) * n) * (countPrim p r S T : ℝ)

theorem primDensity_eq_limUnder (S : Matrix (Fin n) (Fin n) ℤ_[p]) (T : Matrix (Fin m) (Fin m) ℤ_[p]) :
    primDensity p S T = limUnder atTop (normPrim p S T) := rfl

theorem normPrim_eq (S : Matrix (Fin n) (Fin n) ℤ_[p]) (T : Matrix (Fin m) (Fin m) ℤ_[p]) (r : ℕ) :
    normPrim p S T r =
      (p : ℝ) ^ ((r : ℤ) * (((m * (m + 1) / 2 : ℕ) : ℤ) - (m : ℤ) * n)) * (countPrim p r S T : ℝ) := by
  rw [normPrim, ← zpow_natCast, ← _root_.zpow_mul]

theorem normPrim_nonneg (S : Matrix (Fin n) (Fin n) ℤ_[p]) (T : Matrix (Fin m) (Fin m) ℤ_[p]) (r : ℕ) :
    0 ≤ normPrim p S T r := by
  unfold normPrim
  have : (0 : ℝ) < (p : ℝ) ^ r := pow_pos (by exact_mod_cast hp.out.pos) r
  positivity

theorem normPrim_pos_iff (S : Matrix (Fin n) (Fin n) ℤ_[p]) (T : Matrix (Fin m) (Fin m) ℤ_[p]) (r : ℕ) :
    normPrim p S T r ≠ 0 ↔ countPrim p r S T ≠ 0 := by
  unfold normPrim
  have : ((p : ℝ) ^ r) ^ (((m * (m + 1) / 2 : ℕ) : ℤ) - (m : ℤ) * n) ≠ 0 :=
    zpow_ne_zero _ (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero))
  rw [mul_ne_zero_iff, Nat.cast_ne_zero]
  exact ⟨fun h => h.2, fun h => ⟨this, h⟩⟩

/-- **Kitaoka 1993, Lemma 5.6.1 for primitive solutions** (p. 94, used on p. 100): if $r \ge h + 1$ then
$(p^{r+1})^{m(m+1)/2-mn}\#\mathrm{Prim}_{p^{r+1}}(T, S) = (p^r)^{m(m+1)/2-mn}\#\mathrm{Prim}_{p^r}(T, S)$. -/
theorem lemma561_prim {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]} (hS : Sᵀ = S)
    (hT : Tᵀ = T) {h : ℕ} {A : Matrix (Fin m) (Fin m) ℤ_[p]} (hA : T * A = (p : ℤ_[p]) ^ h • 1)
    (hAE : ModE p 0 A) {r : ℕ} (hr : h + 1 ≤ r) : normPrim p S T (r + 1) = normPrim p S T r := by
  have key := countPrim_succ hS hT hA hAE hr
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set M := m * (m + 1) / 2
  have hc : (countPrim p (r + 1) S T : ℝ) = (p : ℝ) ^ ((n : ℤ) * m - M) * countPrim p r S T := by
    have hk : (countPrim p r S T : ℝ) * (p : ℝ) ^ (n * m) = (p : ℝ) ^ M * countPrim p (r + 1) S T := by
      exact_mod_cast key
    rw [zpow_sub₀ hpR, ← Nat.cast_mul, zpow_natCast, zpow_natCast]
    field_simp
    linarith
  rw [normPrim_eq, normPrim_eq, hc, ← mul_assoc, ← zpow_add₀ hpR]
  congr 2
  rw [Nat.cast_add_one]
  ring

theorem normPrim_eq_of_le {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]} (hS : Sᵀ = S)
    (hT : Tᵀ = T) {h : ℕ} {A : Matrix (Fin m) (Fin m) ℤ_[p]} (hA : T * A = (p : ℤ_[p]) ^ h • 1)
    (hAE : ModE p 0 A) {r : ℕ} (hr : h + 1 ≤ r) : normPrim p S T r = normPrim p S T (h + 1) := by
  induction r, hr using Nat.le_induction with
  | base => rfl
  | succ r hr ih => rw [lemma561_prim hS hT hA hAE hr, ih]

/-- **The primitive local density is well defined** (Kitaoka 1993, §5.6, p. 100): for integral symmetric $S$, $T$
and $h$ with $p^hT^{-1} \in E_m$, $d_p(M, N) = (p^r)^{m(m+1)/2-mn}\#\{X \in A_{p^r}(T, S) \mid X \text{ primitive}\}$
for every $r \ge h + 1$. -/
@[kb "kitaoka1993" "§5.6, p. 100 (d_p well-defined)"]
theorem primDensity_eq {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]} (hS : Sᵀ = S)
    (hT : Tᵀ = T) {h : ℕ} {A : Matrix (Fin m) (Fin m) ℤ_[p]} (hA : T * A = (p : ℤ_[p]) ^ h • 1)
    (hAE : ModE p 0 A) {r : ℕ} (hr : h + 1 ≤ r) : primDensity p S T = normPrim p S T r := by
  have ht : Tendsto (normPrim p S T) atTop (nhds (normPrim p S T (h + 1))) :=
    tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨h + 1, fun r hr =>
      (normPrim_eq_of_le hS hT hA hAE hr).symm⟩)
  rw [primDensity_eq_limUnder, ht.limUnder_eq, normPrim_eq_of_le hS hT hA hAE hr]

/-- **The limit defining $d_p(M, N)$ exists** for integral symmetric $S$ and integral symmetric regular $T$; the
sequence is eventually constant. -/
theorem tendsto_normPrim {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]} (hS : Sᵀ = S)
    (hT : Tᵀ = T) (hdet : T.det ≠ 0) : Tendsto (normPrim p S T) atTop (nhds (primDensity p S T)) := by
  obtain ⟨h, A, hA, hAE⟩ := exists_h hT hdet
  rw [primDensity_eq hS hT hA hAE le_rfl]
  exact tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨h + 1, fun r hr =>
    (normPrim_eq_of_le hS hT hA hAE hr).symm⟩)

/-! ### Comparison with $\beta_p$ and the nonvanishing criterion -/

theorem countPrim_le_countA {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]}
    (hS : Sᵀ = S) (hT : Tᵀ = T) (r : ℕ) : countPrim p r S T ≤ countA p r S T := by
  rw [countPrim_eq_card hS hT, countA_eq_card hS hT]
  exact Nat.card_le_card_of_injective (fun X => ⟨X.1, X.2.1⟩) fun X Y hXY =>
    Subtype.ext (Subtype.mk.inj hXY)

/-- **$0 \le d_p(M, N) \le \beta_p(M, N)$** (Kitaoka 1993, §5.6, p. 100): the primitive solutions are among all
solutions. -/
@[kb "kitaoka1993" "§5.6, p. 100 (d_p ≤ β_p)"]
theorem primDensity_le_betaP {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]}
    (hS : Sᵀ = S) (hT : Tᵀ = T) (hdet : T.det ≠ 0) :
    0 ≤ primDensity p S T ∧ primDensity p S T ≤ betaP p S T := by
  obtain ⟨h, A, hA, hAE⟩ := exists_h hT hdet
  rw [primDensity_eq hS hT hA hAE le_rfl, betaP_eq hS hT hA hAE le_rfl]
  refine ⟨normPrim_nonneg S T _, ?_⟩
  unfold normPrim normA
  have : (0 : ℝ) < (p : ℝ) ^ (h + 1) := pow_pos (by exact_mod_cast hp.out.pos) _
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast countPrim_le_countA hS hT _) (by positivity)

/-- **$d_p(M, N) \ne 0$ if and only if there is a primitive isometry** (Kitaoka 1993, §5.6, p. 100: "$d_p(M, N) = 0$
unless there exists an isometry $\sigma : M \to N$ such that $\sigma(M)$ is primitive"): for integral symmetric $S$
and integral symmetric $T$ with $\det T \ne 0$, $d_p(M, N) \ne 0$ if and only if there is
$X \in M_{n,m}(\mathbb Z_p)$ with $X^{\mathsf T}SX = T$ and $X \bmod p$ of rank $m$. -/
@[kb "kitaoka1993" "§5.6, p. 100 (d_p ≠ 0 iff primitive isometry)"]
theorem primDensity_ne_zero_iff {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]}
    (hS : Sᵀ = S) (hT : Tᵀ = T) (hdet : T.det ≠ 0) :
    primDensity p S T ≠ 0 ↔ ∃ X : Matrix (Fin n) (Fin m) ℤ_[p], Xᵀ * S * X = T ∧ IsPrimMat p X := by
  obtain ⟨h, A, hA, hAE⟩ := exists_h hT hdet
  constructor
  · intro hd
    set k := ((4 : ℤ_[p]) * T.det).valuation + 1
    set r := max (h + 1) k
    rw [primDensity_eq hS hT hA hAE (le_max_left (h + 1) k), normPrim_pos_iff] at hd
    unfold countPrim at hd
    obtain ⟨⟨X, hX, hXp⟩⟩ := (Nat.card_ne_zero.mp hd).1
    obtain ⟨V, hVu, hV⟩ := exists_isometry_of_cong hS hT hdet (k := k) (Nat.lt_succ_self _) (liftRes p r X)
      (fun i j => dvd_trans (dvd_trans (pow_dvd_pow _ (le_max_right (h + 1) k)) (dvd_mul_right _ _)) (hX i j))
    obtain ⟨u, rfl⟩ := hVu
    exact ⟨_, hV, (isPrimMat_mul_unit (U := (u : Matrix (Fin m) (Fin m) ℤ_[p])) (V := ↑u⁻¹)
      u.mul_inv).mpr hXp⟩
  · rintro ⟨X, hX, hXp⟩
    rw [primDensity_eq hS hT hA hAE le_rfl, normPrim_pos_iff, countPrim_eq_card hS hT]
    have hmem : GoodA p (h + 1) (h + 1) S T (X.map (red p (h + 1))) ∧
        IsPrimMat p (liftRes p (h + 1) (X.map (red p (h + 1)))) := by
      refine ⟨?_, (isPrimMat_of_mcong (by omega) (mcong_liftRes_red X)).mpr hXp⟩
      rw [GoodA, modE_gram_iff_of_mcong hS (by omega) (mcong_liftRes_red X), hX, sub_self]
      exact ModE.zero
    have : Nonempty {Y // GoodA p (h + 1) (h + 1) S T Y ∧ IsPrimMat p (liftRes p (h + 1) Y)} := ⟨⟨_, hmem⟩⟩
    exact Nat.card_pos.ne'

end QuadFormsKB.Kitaoka.Density
