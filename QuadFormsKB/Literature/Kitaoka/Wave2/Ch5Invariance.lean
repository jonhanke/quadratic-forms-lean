/-
# Kitaoka 1993, §5.6: the local density does not depend on the bases

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §5.6, p. 98 (printed page): the set
$B_{p^r}(M, N; g, p^e)$ of maps $M \to N/p^rN$ "is canonically identified with $B_{p^r}(T, S; G, p^e)$ through matrix
representation. Hence … the following definition of the local density is well-defined."

**Proves** `countA_conj` and `betaP_conj`: for $V \in \mathrm{GL}_n(\mathbb Z_p)$, $W \in \mathrm{GL}_m(\mathbb Z_p)$
(changes of basis of $N$ and $M$), $\#A_{p^r}(W^{\mathsf T}TW, V^{\mathsf T}SV) = \#A_{p^r}(T, S)$ for $r \ge 1$ and
$\beta_p$ is unchanged. So `betaP` is an invariant of the pair of lattices $(M, N)$, as in the book.

*Proof.* $X \mapsto VXW^{-1}$ is a bijection of matrices modulo $p^r$ with
$S[VXW^{-1}] - T = {}^tW^{-1}\bigl((V^{\mathsf T}SV)[X] - W^{\mathsf T}TW\bigr)W^{-1}$; the sequences defining
$\beta_p$ agree from $r = 1$ on, so their limits (`limUnder`) agree.
-/
import QuadFormsKB.Literature.Kitaoka.Wave2.Ch5Stabilization

open Matrix Filter

noncomputable section

namespace QuadFormsKB.Kitaoka.Density

variable {p : ℕ} [hp : Fact p.Prime] {m n : ℕ}

/-- **Change of bases does not change $\#A_{p^r}(T, S)$** ($r \ge 1$). -/
theorem countA_conj {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]} (hS : Sᵀ = S)
    (hT : Tᵀ = T) {V V' : Matrix (Fin n) (Fin n) ℤ_[p]} (hV : V * V' = 1) (hV' : V' * V = 1)
    {W W' : Matrix (Fin m) (Fin m) ℤ_[p]} (hW : W * W' = 1) (hW' : W' * W = 1) {r : ℕ} (hr : 1 ≤ r) :
    countA p r (Vᵀ * S * V) (Wᵀ * T * W) = countA p r S T := by
  have hS' : (Vᵀ * S * V)ᵀ = Vᵀ * S * V := by simp [transpose_mul, hS, Matrix.mul_assoc]
  have hT' : (Wᵀ * T * W)ᵀ = Wᵀ * T * W := by simp [transpose_mul, hT, Matrix.mul_assoc]
  rw [countA_eq_card hS' hT', countA_eq_card hS hT]
  refine Nat.card_congr
    { toFun := fun X => ⟨(V * liftRes p r X.1 * W').map (red p r), ?_⟩
      invFun := fun Y => ⟨(V' * liftRes p r Y.1 * W).map (red p r), ?_⟩
      left_inv := fun X => ?_
      right_inv := fun Y => ?_ }
  · rw [GoodA, modE_gram_iff_of_mcong hS hr (mcong_liftRes_red _)]
    set L := liftRes p r X.1
    have e : (V * L * W')ᵀ * S * (V * L * W') - T =
        W'ᵀ * (Lᵀ * (Vᵀ * S * V) * L - Wᵀ * T * W) * W' := by
      have hI : W'ᵀ * (Wᵀ * T * W) * W' = T := by
        rw [show W'ᵀ * (Wᵀ * T * W) * W' = (W * W')ᵀ * T * (W * W') by
          simp only [transpose_mul, Matrix.mul_assoc], hW, transpose_one, Matrix.one_mul, Matrix.mul_one]
      rw [Matrix.mul_sub, Matrix.sub_mul, hI]
      simp only [transpose_mul, Matrix.mul_assoc]
    rw [e]
    exact X.2.conj W'
  · rw [GoodA, modE_gram_iff_of_mcong hS' hr (mcong_liftRes_red _)]
    set L := liftRes p r Y.1
    have e : (V' * L * W)ᵀ * (Vᵀ * S * V) * (V' * L * W) - Wᵀ * T * W =
        Wᵀ * (Lᵀ * S * L - T) * W := by
      have hI : (V' * L * W)ᵀ * (Vᵀ * S * V) * (V' * L * W) = Wᵀ * (Lᵀ * S * L) * W := by
        rw [show (V' * L * W)ᵀ * (Vᵀ * S * V) * (V' * L * W) =
            Wᵀ * Lᵀ * (V * V')ᵀ * S * (V * V') * L * W by
          simp only [transpose_mul, Matrix.mul_assoc], hV, transpose_one]
        simp only [Matrix.mul_one, Matrix.mul_assoc]
      rw [hI, Matrix.mul_sub, Matrix.sub_mul]
    rw [e]
    exact Y.2.conj W
  · apply Subtype.ext
    have hm : MCong p r (V' * liftRes p r ((V * liftRes p r X.1 * W').map (red p r)) * W)
        (liftRes p r X.1) := by
      obtain ⟨Z, hZ⟩ := mcong_liftRes_red (k := r) (V * liftRes p r X.1 * W')
      refine ⟨V' * Z * W, ?_⟩
      rw [hZ, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc V', ← Matrix.mul_assoc V', hV',
        Matrix.one_mul, Matrix.mul_assoc, hW', Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul]
    exact (red_map_eq_of_mcong hm).trans (red_map_liftRes _)
  · apply Subtype.ext
    have hm : MCong p r (V * liftRes p r ((V' * liftRes p r Y.1 * W).map (red p r)) * W')
        (liftRes p r Y.1) := by
      obtain ⟨Z, hZ⟩ := mcong_liftRes_red (k := r) (V' * liftRes p r Y.1 * W)
      refine ⟨V * Z * W', ?_⟩
      rw [hZ, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc V, ← Matrix.mul_assoc V, hV,
        Matrix.one_mul, Matrix.mul_assoc, hW, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul]
    exact (red_map_eq_of_mcong hm).trans (red_map_liftRes _)

/-- **The local density depends only on the lattices** (Kitaoka 1993, §5.6, p. 98): for changes of basis
$V \in \mathrm{GL}_n(\mathbb Z_p)$ of $N$ and $W \in \mathrm{GL}_m(\mathbb Z_p)$ of $M$,
$\beta_p$ computed from $(W^{\mathsf T}TW, V^{\mathsf T}SV)$ equals $\beta_p$ computed from $(T, S)$. -/
@[kb "kitaoka1993" "§5.6, p. 98 (β_p independent of the bases)"]
theorem betaP_conj {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]} (hS : Sᵀ = S)
    (hT : Tᵀ = T) {V V' : Matrix (Fin n) (Fin n) ℤ_[p]} (hV : V * V' = 1) (hV' : V' * V = 1)
    {W W' : Matrix (Fin m) (Fin m) ℤ_[p]} (hW : W * W' = 1) (hW' : W' * W = 1) :
    betaP p (Vᵀ * S * V) (Wᵀ * T * W) = betaP p S T := by
  rw [betaP_eq_limUnder, betaP_eq_limUnder]
  have h : normA p (Vᵀ * S * V) (Wᵀ * T * W) =ᶠ[atTop] normA p S T :=
    eventually_atTop.mpr ⟨1, fun r hr => by rw [normA, normA, countA_conj hS hT hV hV' hW hW' hr]⟩
  simp only [limUnder]
  rw [Filter.map_congr h]

end QuadFormsKB.Kitaoka.Density
