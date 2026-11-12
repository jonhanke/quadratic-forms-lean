/-
# Kitaoka 1993, Theorem 5.6.4 (b), (c): local densities and inclusions of lattices

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §5.6, Theorem 5.6.4 (b), (c), pp. 115–116 (printed
pages).

**Setting** as in `Ch5Densities.lean`: $N \subseteq N'$ means $S = C^{\mathsf T}S'C$ for the Gram matrices $S$, $S'$
of $N$, $N'$ and the matrix $C$ ($\det C \ne 0$) expressing a basis of $N$ in a basis of $N'$; then
$[N' : N] = \|\det C\|^{-1}$ ($\|\cdot\|$ the $p$-adic norm).

**Proves**
* `countA_le_of_incl`: $\#A_{p^t}(T, S) \le [N' : N]^m\,\#A_{p^t}(T, S')$ for $t \ge 1$;
* `theorem564b : Theorem564b` (Theorem 5.6.4 (b)): $\beta_p(M, N) \le [N' : N]^m\beta_p(M, N')$;
* `theorem564c : Theorem564c` (Theorem 5.6.4 (c)): $\beta_p(M, N') \le p^{-rm(m+1)}[N : p^rN']^m\beta_p(p^rM, N)$.

*Proof (Kitaoka's).* (b): $X \mapsto CX$ maps $A_{p^t}(T, S)$ into $A_{p^t}(T, S')$ ($S'[CX] = S[X]$); two $X$ with the
same image differ by $Y$ with $CY \equiv 0 \bmod p^t$, and there are at most $\|\det C\|^{-m}$ such $Y$ modulo $p^t$
(`card_ker_mat_le`, `Ch5KernelCount.lean`). Divide by $(p^t)^{mn - m(m+1)/2}$ and let $t \to \infty$ (both limits
exist, `tendsto_normA`). (c): by (a) (`betaP_scale`) $\beta_p(M, N') = p^{-rm(m+1)}\beta_p(p^rM, p^rN')$, and (b) for
$p^rN' \subseteq N$ (matrix $C''$, Gram matrix $C''^{\mathsf T}SC'' = p^{2r}S'$).

The hypotheses $m \le n$ and $\det S' \ne 0$ of the statements are not used; $T$ must be regular (so that the limits
exist) and $S'$ symmetric.
-/
import QuadFormsKB.Literature.Kitaoka.Wave2.Ch5Stabilization
import QuadFormsKB.Literature.Kitaoka.Wave2.Ch5KernelCount

open Matrix Filter

noncomputable section

namespace QuadFormsKB.Kitaoka.Density

variable {p : ℕ} [hp : Fact p.Prime] {m n : ℕ}

/-- **The counting step of Theorem 5.6.4 (b)** (Kitaoka, p. 116): for $S = C^{\mathsf T}S'C$, $\det C \ne 0$ and
$t \ge 1$, $\#A_{p^t}(T, S) \le \|\det C\|^{-m}\#A_{p^t}(T, S')$. -/
theorem countA_le_of_incl {S' C : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]} (hS' : S'ᵀ = S')
    (hT : Tᵀ = T) (hC : C.det ≠ 0) {t : ℕ} (ht : 1 ≤ t) :
    (countA p t (Cᵀ * S' * C) T : ℝ) ≤ ‖C.det‖⁻¹ ^ m * countA p t S' T := by
  classical
  have hS : (Cᵀ * S' * C)ᵀ = Cᵀ * S' * C := by simp [transpose_mul, hS', Matrix.mul_assoc]
  rw [countA_eq_card hS hT, countA_eq_card hS' hT]
  set L := liftRes p t (n := n) (m := m)
  let Φ : Matrix (Fin n) (Fin m) (Fin (p ^ t)) → Matrix (Fin n) (Fin m) (Fin (p ^ t)) := fun X =>
    (C * L X).map (red p t)
  have hΦ : ∀ X, GoodA p t t (Cᵀ * S' * C) T X → GoodA p t t S' T (Φ X) := by
    intro X hX
    simp only [GoodA] at hX ⊢
    rw [modE_gram_iff_of_mcong hS' ht (mcong_liftRes_red _)]
    convert hX using 2
    simp only [transpose_mul, Matrix.mul_assoc]; rfl
  have : Nonempty (Matrix (Fin n) (Fin m) (Fin (p ^ t))) := ⟨fun _ _ => ⟨0, pow_pos hp.out.pos t⟩⟩
  let s : Matrix (Fin n) (Fin m) (Fin (p ^ t)) → Matrix (Fin n) (Fin m) (Fin (p ^ t)) := fun X' =>
    Classical.epsilon fun Z => Φ Z = X'
  have hs : ∀ X, Φ (s (Φ X)) = Φ X := fun X => Classical.epsilon_spec (p := fun Z => Φ Z = Φ X) ⟨X, rfl⟩
  -- the difference of two matrices with the same image lies in the kernel
  have hK : ∀ X Z, Φ X = Φ Z → ∀ i j, (p : ℤ_[p]) ^ t ∣ (C * L ((L X - L Z).map (red p t))) i j := by
    intro X Z hXZ i j
    obtain ⟨W, hW⟩ := mcong_liftRes_red (k := t) (L X - L Z)
    have hd : (p : ℤ_[p]) ^ t ∣ (C * L X) i j - (C * L Z) i j := by
      have := congrFun (congrFun hXZ i) j
      simp only [Φ, Matrix.map_apply] at this
      exact red_eq_iff.mp this
    have e : C * L ((L X - L Z).map (red p t)) = C * L X - C * L Z + (p : ℤ_[p]) ^ t • (C * W) := by
      rw [show L ((L X - L Z).map (red p t)) = liftRes p t ((L X - L Z).map (red p t)) from rfl, hW,
        Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul]
    rw [e, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    exact dvd_add hd (dvd_mul_right _ _)
  let K := {Y : Matrix (Fin n) (Fin m) (Fin (p ^ t)) //
    ∀ i j, (p : ℤ_[p]) ^ t ∣ (C * Y.map fun a => (((a : ℕ)) : ℤ_[p])) i j}
  let f : {X // GoodA p t t (Cᵀ * S' * C) T X} → {X' // GoodA p t t S' T X'} × K := fun X =>
    (⟨Φ X.1, hΦ X.1 X.2⟩, ⟨(L X.1 - L (s (Φ X.1))).map (red p t), hK X.1 (s (Φ X.1)) (hs X.1).symm⟩)
  have hf : Function.Injective f := by
    rintro ⟨X, hX⟩ ⟨Y, hY⟩ hXY
    simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at hXY
    obtain ⟨h1, h2⟩ := hXY
    have h1v : Φ X = Φ Y := h1
    have h2v : (L X - L (s (Φ Y))).map (red p t) = (L Y - L (s (Φ Y))).map (red p t) := by
      have h2c : (L X - L (s (Φ X))).map (red p t) = (L Y - L (s (Φ Y))).map (red p t) :=
        congrArg Subtype.val h2
      rwa [h1v] at h2c
    apply Subtype.ext
    simp only
    rw [← red_map_liftRes X, ← red_map_liftRes Y]
    refine Matrix.ext fun i j => ?_
    have := congrFun (congrFun h2v i) j
    simp only [Matrix.map_apply, Matrix.sub_apply] at this ⊢
    obtain ⟨c, hc⟩ := red_eq_iff.mp this
    exact red_eq_iff.mpr ⟨c, by rw [← hc]; ring⟩
  have h1 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod] at h1
  have h2 := card_ker_mat_le C hC t m
  have h0 : (0 : ℝ) ≤ Nat.card {X' // GoodA p t t S' T X'} := Nat.cast_nonneg _
  calc (Nat.card {X // GoodA p t t (Cᵀ * S' * C) T X} : ℝ)
      ≤ (Nat.card {X' // GoodA p t t S' T X'} : ℝ) * Nat.card K := by exact_mod_cast h1
    _ ≤ (Nat.card {X' // GoodA p t t S' T X'} : ℝ) * ‖C.det‖⁻¹ ^ m := mul_le_mul_of_nonneg_left h2 h0
    _ = _ := mul_comm _ _

/-- **Kitaoka 1993, Theorem 5.6.4 (b)** (p. 115), *proved*: if $N \subseteq N'$ then
$\beta_p(M, N) \le [N' : N]^m\beta_p(M, N')$. -/
@[kb "kitaoka1993" "§5.6, Thm. 5.6.4 (b), p. 115"]
theorem theorem564b : Theorem564b := by
  intro p _ m n T S' C _ hT hS' hC
  have hS : (Cᵀ * S' * C)ᵀ = Cᵀ * S' * C := by simp [transpose_mul, hS'.1.eq, Matrix.mul_assoc]
  have h1 := tendsto_normA (p := p) hS hT.1 hT.2
  have h2 := (tendsto_normA (p := p) hS'.1 hT.1 hT.2).const_mul (‖C.det‖⁻¹ ^ m)
  refine le_of_tendsto_of_tendsto h1 h2 (eventually_atTop.mpr ⟨1, fun t ht => ?_⟩)
  simp only [normA]
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (countA_le_of_incl hS'.1 hT.1 hC ht) (by positivity)

/-- **Kitaoka 1993, Theorem 5.6.4 (c)** (p. 115), *proved*: if $N \subseteq N'$ and $p^rN' \subseteq N$ then
$\beta_p(M, N') \le p^{-rm(m+1)}[N : p^rN']^m\beta_p(p^rM, N)$. -/
@[kb "kitaoka1993" "§5.6, Thm. 5.6.4 (c), p. 115"]
theorem theorem564c : Theorem564c := by
  intro p _ m n r T S' C C'' hmn hT hS' hCC
  have hp0 : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hdetCC : C.det * C''.det ≠ 0 := by
    rw [← det_mul, hCC, det_smul, det_one, mul_one]
    exact pow_ne_zero _ (pow_ne_zero _ hp0)
  have hC'' : C''.det ≠ 0 := right_ne_zero_of_mul hdetCC
  have hC : C.det ≠ 0 := left_ne_zero_of_mul hdetCC
  have hS : IsRegGram (Cᵀ * S' * C) := by
    refine ⟨?_, ?_⟩
    · show (Cᵀ * S' * C)ᵀ = Cᵀ * S' * C
      simp [transpose_mul, hS'.1.eq, Matrix.mul_assoc]
    · rw [det_mul, det_mul, det_transpose]
      exact mul_ne_zero (mul_ne_zero hC hS'.2) hC
  have hT' : IsRegGram ((p : ℤ_[p]) ^ (2 * r) • T) := by
    refine ⟨?_, ?_⟩
    · show ((p : ℤ_[p]) ^ (2 * r) • T)ᵀ = (p : ℤ_[p]) ^ (2 * r) • T
      rw [transpose_smul, hT.1.eq]
    · rw [det_smul]
      exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hp0)) hT.2
  have key : C''ᵀ * (Cᵀ * S' * C) * C'' = (p : ℤ_[p]) ^ (2 * r) • S' := by
    calc C''ᵀ * (Cᵀ * S' * C) * C'' = (C * C'')ᵀ * S' * (C * C'') := by
          simp only [transpose_mul, Matrix.mul_assoc]
      _ = _ := by
          rw [hCC, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
            Matrix.mul_one, smul_smul, ← pow_add, two_mul]
  have hb := theorem564b p m n ((p : ℤ_[p]) ^ (2 * r) • T) (Cᵀ * S' * C) C'' hmn hT' hS hC''
  rw [key] at hb
  have ha := betaP_scale hS'.1 hT.1 hT.2 (2 * r)
  have hexp : 2 * r * (m * (m + 1) / 2) = r * m * (m + 1) := by
    have : 2 * (m * (m + 1) / 2) = m * (m + 1) := Nat.mul_div_cancel' (Nat.even_mul_succ_self m).two_dvd
    rw [mul_comm 2 r, mul_assoc, this, mul_assoc]
  have hpR : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [hexp] at ha
  calc betaP p S' T = (p : ℝ) ^ (-((r * m * (m + 1) : ℕ) : ℤ)) *
        betaP p ((p : ℤ_[p]) ^ (2 * r) • S') ((p : ℤ_[p]) ^ (2 * r) • T) := by
        rw [ha, ← mul_assoc, _root_.zpow_neg, zpow_natCast, inv_mul_cancel₀ (by positivity), one_mul]
    _ ≤ _ := by
        exact (mul_le_mul_of_nonneg_left hb (zpow_pos hpR _).le).trans_eq (by ring)

end QuadFormsKB.Kitaoka.Density
