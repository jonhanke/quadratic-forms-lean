/-
# Kitaoka 1993, Lemma 5.6.3 (integral case): $\#A_{p^r}(T, S) = p^{t\operatorname{ord}_p\det S}\#B_{p^r}(T, S)$

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §5.6, Lemma 5.6.3, pp. 95–96 (printed pages), the
second assertion, case $e = 0$.

**Book statement.** For regular symmetric $S$ (degree $s$) and $T$ (degree $t$) over $F = \mathbb Q_p$ put
$$B_{p^r}(T, S) = \{X \in M_{s,t}(R) \bmod p^rS^{-1}M_{s,t}(R) \mid S[X] \equiv T \bmod p^rE_t(R)\},$$
and let $h'$ be an integer with $p^{h'}S^{-1} \in E_s(R)$. "Moreover if $S$ and $T$ are integral and
$r > h' + \max(e, 1)$, then $\#A_{p^r}(T, S) = p^{t\operatorname{ord}_p(\det S)}\#B_{p^r}(T, S)$."

**Encoding.** $S$ ($n \times n$) and $T$ ($m \times m$) are integral symmetric, $\det S \ne 0$, and $h'$ is given by
$SA' = p^{h'}1$ with $A' \in E_n$ (`ModE p 0 A'`). For $r \ge h'$, $p^rS^{-1}M_{n,m}(R) \subseteq M_{n,m}(R)$ contains
$p^rM_{n,m}(R)$, so $B_{p^r}(T, S)$ is the set of elements of $A_{p^r}(T, S)$ (residues modulo $p^r$) up to the
relation $X \sim X' \iff S(X - X') \equiv 0 \bmod p^r$, i.e. $X - X' \in p^rS^{-1}M_{n,m}(R)$ (`bSetoid`, `countB`).

**Proves** `lemma563` for $r \ge \max(h', 1)$ (the book: $r > h' + 1$).

*Proof.* If $X$ satisfies $S[X] \equiv T \bmod p^rE_m$ and $S D = p^rY$, then
$S[X + D] - S[X] = F + F^{\mathsf T} + D^{\mathsf T}SD$ with $F = p^rX^{\mathsf T}Y$, and
$D^{\mathsf T}SD = p^{2r-h'}Y^{\mathsf T}A'Y \in p^rE_m$; so the condition is constant on classes. Each class is a
coset of the kernel $\{Z \bmod p^r \mid SZ \equiv 0 \bmod p^r\}$, which has exactly
$|\det S|_p^{-m} = p^{m\operatorname{ord}_p\det S}$ elements (`card_ker_mat_eq'`, using $S \cdot p^{r-h'}A' = p^r1$).

The result is unconditional (no named input hypotheses).
-/
import QuadFormsKB.Literature.Kitaoka.Wave3.Ch5Theorem564e

open Matrix

noncomputable section

namespace QuadFormsKB.Kitaoka.Density

variable {p : ℕ} [hp : Fact p.Prime] {m n : ℕ}

/-- The relation $X \sim X' \iff S(X - X') \equiv 0 \bmod p^r$ on residue matrices modulo $p^r$, i.e.
$X \equiv X' \bmod p^rS^{-1}M_{n,m}(R)$. -/
def bSetoid (p : ℕ) [Fact p.Prime] (r : ℕ) (S : Matrix (Fin n) (Fin n) ℤ_[p]) (P : Matrix (Fin n) (Fin m) (Fin (p ^ r)) → Prop) :
    Setoid {X // P X} where
  r X X' := ∀ i j, (p : ℤ_[p]) ^ r ∣ (S * (liftRes p r X.1 - liftRes p r X'.1)) i j
  iseqv :=
    { refl := fun X i j => by simp
      symm := fun {X X'} h i j => by
        have := h i j
        rw [← neg_sub, Matrix.mul_neg, Matrix.neg_apply]
        exact (dvd_neg).mpr this
      trans := fun {X X' X''} h h' i j => by
        have := dvd_add (h i j) (h' i j)
        rwa [← Matrix.add_apply, ← Matrix.mul_add, sub_add_sub_cancel] at this }

/-- **$\#B_{p^r}(T, S)$** (Kitaoka 1993, Lemma 5.6.3, p. 95, $e = 0$, integral $S$): the elements of
$A_{p^r}(T, S)$ up to $X \equiv X' \bmod p^rS^{-1}M_{n,m}(R)$. -/
@[kb "kitaoka1993" "§5.6, Lemma 5.6.3, p. 95 (B_{p^r}(T, S))"]
def countB (p : ℕ) [Fact p.Prime] (r : ℕ) (S : Matrix (Fin n) (Fin n) ℤ_[p]) (T : Matrix (Fin m) (Fin m) ℤ_[p]) :
    ℕ :=
  Nat.card (Quotient (bSetoid p r S fun X : Matrix (Fin n) (Fin m) (Fin (p ^ r)) =>
    ∀ i j, ((p : ℤ_[p]) ^ r * if i = j then 2 else 1) ∣ ((liftRes p r X)ᵀ * S * liftRes p r X - T) i j))

/-- The condition $S[X] \equiv T \bmod p^rE_m$ is unchanged by $X \mapsto X + D$ when $SD \equiv 0 \bmod p^r$ and
$r \ge h'$. -/
theorem modE_add_of_ker {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]} (hS : Sᵀ = S)
    {h' : ℕ} {A' : Matrix (Fin n) (Fin n) ℤ_[p]} (hA : S * A' = (p : ℤ_[p]) ^ h' • 1) (hAE : ModE p 0 A')
    {r : ℕ} (hr : h' ≤ r) {X D Y : Matrix (Fin n) (Fin m) ℤ_[p]} (hD : S * D = (p : ℤ_[p]) ^ r • Y)
    (hX : ModE p r (Xᵀ * S * X - T)) : ModE p r ((X + D)ᵀ * S * (X + D) - T) := by
  obtain ⟨G, hG⟩ := hAE
  rw [pow_zero, one_smul] at hG
  have hAs : A'ᵀ = A' := by rw [hG]; simp [add_comm]
  have hAS : A' * S = (p : ℤ_[p]) ^ h' • 1 := by
    have := congrArg transpose hA
    rwa [transpose_mul, hS, hAs, transpose_smul, transpose_one] at this
  -- `p^{h'} D = p^r A' Y`
  have hD' : (p : ℤ_[p]) ^ h' • D = (p : ℤ_[p]) ^ r • (A' * Y) := by
    calc (p : ℤ_[p]) ^ h' • D = ((p : ℤ_[p]) ^ h' • (1 : Matrix (Fin n) (Fin n) ℤ_[p])) * D := by
          rw [Matrix.smul_mul, Matrix.one_mul]
      _ = (p : ℤ_[p]) ^ r • (A' * Y) := by rw [← hAS, Matrix.mul_assoc, hD, Matrix.mul_smul]
  -- `DᵀSD = p^{2r-h'} YᵀA'Y`
  have hp0 : ((p : ℤ_[p]) ^ (2 * h')) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have hYAY : Yᵀ * A' * S * A' * Y = (p : ℤ_[p]) ^ h' • (Yᵀ * A' * Y) := by
    rw [Matrix.mul_assoc (Yᵀ * A') S A', hA, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  have hDSD : Dᵀ * S * D = (p : ℤ_[p]) ^ (2 * r - h') • (Yᵀ * A' * Y) := by
    apply smul_right_injective (Matrix (Fin m) (Fin m) ℤ_[p]) hp0
    have e1 : (p : ℤ_[p]) ^ (2 * h') • (Dᵀ * S * D) =
        ((p : ℤ_[p]) ^ h' • D)ᵀ * S * ((p : ℤ_[p]) ^ h' • D) := by
      simp only [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_add, two_mul]
    have e2 : ((p : ℤ_[p]) ^ r • (A' * Y))ᵀ * S * ((p : ℤ_[p]) ^ r • (A' * Y)) =
        ((p : ℤ_[p]) ^ r * (p : ℤ_[p]) ^ r) • (Yᵀ * A' * S * A' * Y) := by
      simp only [transpose_smul, transpose_mul, hAs, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        Matrix.mul_assoc]
    change (p : ℤ_[p]) ^ (2 * h') • (Dᵀ * S * D) =
      (p : ℤ_[p]) ^ (2 * h') • ((p : ℤ_[p]) ^ (2 * r - h') • (Yᵀ * A' * Y))
    rw [e1, hD', e2, hYAY, smul_smul, smul_smul, ← pow_add, ← pow_add, ← pow_add]
    congr 2
    omega
  have hexp : (X + D)ᵀ * S * (X + D) - T = (Xᵀ * S * X - T) +
      ((p : ℤ_[p]) ^ r • (Xᵀ * Y) + ((p : ℤ_[p]) ^ r • (Xᵀ * Y))ᵀ) + Dᵀ * S * D := by
    have h1 : Xᵀ * S * D = (p : ℤ_[p]) ^ r • (Xᵀ * Y) := by rw [Matrix.mul_assoc, hD, Matrix.mul_smul]
    have h2 : (Xᵀ * S * D)ᵀ = Dᵀ * S * X := by
      rw [transpose_mul, transpose_mul, transpose_transpose, hS, Matrix.mul_assoc]
    rw [← h1, h2]
    simp only [transpose_add, Matrix.add_mul, Matrix.mul_add]
    abel
  rw [hexp]
  refine (hX.add ⟨Xᵀ * Y, by rw [transpose_smul, smul_add]⟩).add ?_
  rw [hDSD]
  have := (ModE.conj (⟨G, by rw [pow_zero, one_smul]; exact hG⟩ : ModE p 0 A') Y).smul_pow (2 * r - h')
  rw [zero_add] at this
  exact this.mono (by omega)

/-- **Kitaoka 1993, Lemma 5.6.3** (p. 96), second assertion, case $e = 0$: for integral symmetric $S$
($n \times n$, $\det S \ne 0$) and $T$ ($m \times m$), and $h'$ with $p^{h'}S^{-1} \in E_n$ ($SA' = p^{h'}1$,
$A' \in E_n$),
$$\#A_{p^r}(T, S) = p^{m\operatorname{ord}_p(\det S)}\#B_{p^r}(T, S) \qquad (r \ge \max(h', 1)).$$
*Update:* the book assumes $r > h' + \max(e, 1)$. -/
@[kb "kitaoka1993" "§5.6, Lemma 5.6.3, p. 96"]
theorem lemma563 {S : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]} (hS : Sᵀ = S)
    (hT : Tᵀ = T) (hdet : S.det ≠ 0) {h' : ℕ} {A' : Matrix (Fin n) (Fin n) ℤ_[p]}
    (hA : S * A' = (p : ℤ_[p]) ^ h' • 1) (hAE : ModE p 0 A') {r : ℕ} (hr : h' ≤ r) (hr1 : 1 ≤ r) :
    countA p r S T = p ^ (m * S.det.valuation) * countB p r S T := by
  classical
  set P : Matrix (Fin n) (Fin m) (Fin (p ^ r)) → Prop := fun X =>
    ∀ i j, ((p : ℤ_[p]) ^ r * if i = j then 2 else 1) ∣ ((liftRes p r X)ᵀ * S * liftRes p r X - T) i j
  have hPG : ∀ X, P X ↔ GoodA p r r S T X := fun X => by
    rw [GoodA, modE_iff_dvd (by simp [transpose_sub, transpose_mul, hS, hT, Matrix.mul_assoc])]
  let K := {Z : Matrix (Fin n) (Fin m) (Fin (p ^ r)) //
    ∀ i j, (p : ℤ_[p]) ^ r ∣ (S * Z.map fun a => (((a : ℕ)) : ℤ_[p])) i j}
  have hK : ∀ Z : Matrix (Fin n) (Fin m) (Fin (p ^ r)),
      (∀ i j, (p : ℤ_[p]) ^ r ∣ (S * Z.map fun a => (((a : ℕ)) : ℤ_[p])) i j) ↔
        MCong p r (S * liftRes p r Z) 0 := by
    intro Z
    rw [mcong_iff_dvd]
    simp [liftRes]
  set σ := bSetoid p r S P
  have hrel : ∀ X X' : {X // P X}, σ X X' ↔ MCong p r (S * liftRes p r X.1) (S * liftRes p r X'.1) := by
    intro X X'
    rw [mcong_iff_dvd]
    change (∀ i j, (p : ℤ_[p]) ^ r ∣ (S * (liftRes p r X.1 - liftRes p r X'.1)) i j) ↔ _
    rw [Matrix.mul_sub]
  have hfib : ∀ q : Quotient σ, Nonempty ({X : {X // P X} // Quotient.mk σ X = q} ≃ K) := by
    intro q
    induction q using Quotient.inductionOn with
    | h X0 =>
    have hgood : ∀ Z : K, P ((liftRes p r X0.1 + liftRes p r Z.1).map (red p r)) := by
      intro Z
      rw [hPG, GoodA, modE_gram_iff_of_mcong hS hr1 (mcong_liftRes_red _)]
      obtain ⟨Y, hY⟩ := (hK Z.1).mp Z.2
      rw [zero_add] at hY
      exact modE_add_of_ker hS hA hAE hr hY ((hPG _).mp X0.2)
    refine ⟨{ toFun := fun X => ⟨(liftRes p r X.1.1 - liftRes p r X0.1).map (red p r), ?_⟩
              invFun := fun Z => ⟨⟨_, hgood Z⟩, ?_⟩
              left_inv := fun X => ?_
              right_inv := fun Z => ?_ }⟩
    · rw [hK]
      have h1 := (mcong_liftRes_red (k := r) (liftRes p r X.1.1 - liftRes p r X0.1)).mul_left S
      refine h1.trans' ?_
      rw [Matrix.mul_sub]
      have := ((hrel X.1 X0).mp (Quotient.exact X.2)).sub (MCong.refl' (S * liftRes p r X0.1))
      rwa [sub_self] at this
    · apply Quotient.sound
      apply (hrel _ _).mpr
      have h1 := (mcong_liftRes_red (k := r) (liftRes p r X0.1 + liftRes p r Z.1)).mul_left S
      refine h1.trans' ?_
      rw [Matrix.mul_add]
      have := (MCong.refl' (S * liftRes p r X0.1)).add ((hK Z.1).mp Z.2)
      rwa [add_zero] at this
    · apply Subtype.ext; apply Subtype.ext
      change (liftRes p r X0.1 + liftRes p r ((liftRes p r X.1.1 - liftRes p r X0.1).map (red p r))).map
        (red p r) = X.1.1
      conv_rhs => rw [← red_map_liftRes X.1.1]
      apply red_map_eq_iff.mpr
      have h1 := (MCong.refl' (liftRes p r X0.1)).add
        (mcong_liftRes_red (k := r) (liftRes p r X.1.1 - liftRes p r X0.1))
      rwa [add_sub_cancel] at h1
    · apply Subtype.ext
      change (liftRes p r ((liftRes p r X0.1 + liftRes p r Z.1).map (red p r)) - liftRes p r X0.1).map
        (red p r) = Z.1
      conv_rhs => rw [← red_map_liftRes Z.1]
      apply red_map_eq_iff.mpr
      have h1 := (mcong_liftRes_red (k := r) (liftRes p r X0.1 + liftRes p r Z.1)).sub
        (MCong.refl' (liftRes p r X0.1))
      rwa [add_sub_cancel_left] at h1
  have hcard : Nat.card {X // P X} = Nat.card (Quotient σ) * Nat.card K := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (Quotient.mk σ)), Nat.card_sigma,
      Finset.sum_congr rfl fun q _ => Nat.card_congr (hfib q).some, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, Nat.card_eq_fintype_card (α := Quotient σ)]
  have hKc : (Nat.card K : ℝ) = ‖S.det‖⁻¹ ^ m :=
    card_ker_mat_eq' S hdet r m ⟨(p : ℤ_[p]) ^ (r - h') • A', by
      rw [Matrix.mul_smul, hA, smul_smul, ← pow_add, Nat.sub_add_cancel hr]⟩
  have hnorm : ‖S.det‖⁻¹ = (p : ℝ) ^ S.det.valuation := by
    rw [PadicInt.norm_eq_zpow_neg_valuation hdet, _root_.zpow_neg, inv_inv, zpow_natCast]
  have hK' : Nat.card K = p ^ (m * S.det.valuation) := by
    have : (Nat.card K : ℝ) = ((p ^ (m * S.det.valuation) : ℕ) : ℝ) := by
      rw [hKc, hnorm]; push_cast; rw [← pow_mul, mul_comm]
    exact_mod_cast this
  change Nat.card {X // P X} = _
  rw [hcard, hK', mul_comm]
  rfl

end QuadFormsKB.Kitaoka.Density
