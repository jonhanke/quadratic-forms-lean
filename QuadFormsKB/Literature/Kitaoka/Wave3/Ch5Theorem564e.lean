/-
# Kitaoka 1993, Theorem 5.6.4 (e): passing to a sublattice that contains every image of $M$

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §5.6, Theorem 5.6.4 (e), p. 116 (printed page),
statement `Theorem564e` in `Ch5Densities.lean`.

**Statement.** Let $N' \subseteq N$ be lattices of rank $n$ and $M$ a regular lattice of rank $m \le n$. If
$\eta(M) \subseteq N'$ for every isometry $\eta : M \rightarrowtail N$, then
$\beta_p(M, N) = [N : N']^{-m}\beta_p(M, N')$. In matrix terms: $N'$ has Gram matrix $S' = C^{\mathsf T}SC$ with
$\det C \ne 0$, $[N : N'] = |\det C|_p^{-1}$, and the hypothesis says that every $X$ with $S[X] = T$ is $X = CY$ with
$Y$ integral.

**Proves** `theorem564e : Theorem564e`, through the counting identity `countA_factor`:
$$\#A_{p^r}(T, C^{\mathsf T}SC) = |\det C|_p^{-m}\,\#A_{p^r}(T, S)$$
for $r$ large ($r \ge 1$, $r > \operatorname{ord}_p(4\det T)$ and $\det C \mid p^r$).

*Proof of the counting identity.* The map $\Phi : Y \mapsto CY \bmod p^r$ sends $A_{p^r}(T, S')$ to $A_{p^r}(T, S)$,
since $S'[Y] = S[CY]$. It is onto: an $X \in A_{p^r}(T, S)$ satisfies $S[X] \equiv T \bmod p^r$, so by Cassels'
lemma (`exists_isometry_of_cong`) $XV$ is an exact isometry for an invertible $V$, hence $XV = CY_1$ by hypothesis and
$X = \Phi(Y_1V^{-1})$. Two residues $Y, Y'$ have the same image exactly when $C(Y - Y') \equiv 0 \bmod p^r$, and then
both lie in $A_{p^r}(T, S')$ or neither does. So every fiber is a coset of the kernel
$\{Z \bmod p^r \mid CZ \equiv 0 \bmod p^r\}$, which has exactly $|\det C|_p^{-m}$ elements once $\det C \mid p^r$
(`card_ker_mat_eq`). Kitaoka's own proof goes through Theorem 5.6.4 (b) and (c) and the description of
$A_{p^r}(T, S)$ by maps $M \to N/p^rN$; the counting here is a direct version of the same idea.

The result is unconditional (no named input hypotheses). *Update:* the hypotheses
$m \le n$ and $\det S \ne 0$ of the statement are not used.
-/
import QuadFormsKB.Literature.Kitaoka.Wave3.Ch5Exercise
import QuadFormsKB.Literature.Kitaoka.Wave3.Ch5KernelExact

open Matrix Filter

noncomputable section

namespace QuadFormsKB.Kitaoka.Density

variable {p : ℕ} [hp : Fact p.Prime] {m n : ℕ}

theorem MCong.mul_left {a b c k : ℕ} {X X' : Matrix (Fin b) (Fin c) ℤ_[p]} (h : MCong p k X X')
    (C : Matrix (Fin a) (Fin b) ℤ_[p]) : MCong p k (C * X) (C * X') := by
  obtain ⟨Y, rfl⟩ := h
  exact ⟨C * Y, by rw [Matrix.mul_add, Matrix.mul_smul]⟩

theorem MCong.symm' {a b k : ℕ} {X X' : Matrix (Fin a) (Fin b) ℤ_[p]} (h : MCong p k X X') : MCong p k X' X := by
  obtain ⟨Y, rfl⟩ := h
  exact ⟨-Y, by rw [smul_neg, add_neg_cancel_right]⟩

theorem MCong.trans' {a b k : ℕ} {X X' X'' : Matrix (Fin a) (Fin b) ℤ_[p]} (h : MCong p k X X')
    (h' : MCong p k X' X'') : MCong p k X X'' := by
  obtain ⟨Y, rfl⟩ := h
  obtain ⟨Y', rfl⟩ := h'
  exact ⟨Y' + Y, by rw [smul_add, add_assoc]⟩

theorem MCong.refl' {a b k : ℕ} (X : Matrix (Fin a) (Fin b) ℤ_[p]) : MCong p k X X :=
  ⟨0, by rw [smul_zero, add_zero]⟩

theorem MCong.add {a b k : ℕ} {X X' Z Z' : Matrix (Fin a) (Fin b) ℤ_[p]} (h : MCong p k X X')
    (h' : MCong p k Z Z') : MCong p k (X + Z) (X' + Z') := by
  obtain ⟨Y, rfl⟩ := h
  obtain ⟨Y', rfl⟩ := h'
  exact ⟨Y + Y', by rw [smul_add]; abel⟩

theorem MCong.sub {a b k : ℕ} {X X' Z Z' : Matrix (Fin a) (Fin b) ℤ_[p]} (h : MCong p k X X')
    (h' : MCong p k Z Z') : MCong p k (X - Z) (X' - Z') := by
  obtain ⟨Y, rfl⟩ := h
  obtain ⟨Y', rfl⟩ := h'
  exact ⟨Y - Y', by rw [smul_sub]; abel⟩

theorem mcong_iff_dvd {a b k : ℕ} {X X' : Matrix (Fin a) (Fin b) ℤ_[p]} :
    MCong p k X X' ↔ ∀ i j, (p : ℤ_[p]) ^ k ∣ (X - X') i j := by
  constructor
  · rintro ⟨Y, rfl⟩ i j
    exact ⟨Y i j, by simp⟩
  · intro h
    choose w hw using h
    exact ⟨Matrix.of w, by refine Matrix.ext fun i j => ?_; have := hw i j; simp at this ⊢; linear_combination this⟩

theorem red_map_eq_iff {a b k : ℕ} {X X' : Matrix (Fin a) (Fin b) ℤ_[p]} :
    X.map (red p k) = X'.map (red p k) ↔ MCong p k X X' := by
  rw [mcong_iff_dvd]
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    simp only [Matrix.map_apply] at this
    rw [Matrix.sub_apply]
    exact red_eq_iff.mp this
  · intro h
    ext i j
    simp only [Matrix.map_apply]
    have := red_eq_iff.mpr (by simpa using h i j)
    rw [this]

theorem dvd_of_modE {k : ℕ} {D : Matrix (Fin m) (Fin m) ℤ_[p]} (h : ModE p k D) (i j : Fin m) :
    (p : ℤ_[p]) ^ k ∣ D i j := by
  obtain ⟨F, rfl⟩ := h
  exact ⟨(F + Fᵀ) i j, by simp⟩

/-- The map $\Phi : Y \mapsto CY \bmod p^r$ on residue matrices. -/
def phiC (C : Matrix (Fin n) (Fin n) ℤ_[p]) (r : ℕ) (Y : Matrix (Fin n) (Fin m) (Fin (p ^ r))) :
    Matrix (Fin n) (Fin m) (Fin (p ^ r)) :=
  (C * liftRes p r Y).map (red p r)

/-- **The counting identity behind Theorem 5.6.4 (e).** -/
theorem countA_factor {S C : Matrix (Fin n) (Fin n) ℤ_[p]} {T : Matrix (Fin m) (Fin m) ℤ_[p]} (hS : Sᵀ = S)
    (hT : Tᵀ = T) (hdet : T.det ≠ 0) (hC : C.det ≠ 0)
    (hfac : ∀ X : Matrix (Fin n) (Fin m) ℤ_[p], Xᵀ * S * X = T → ∃ Y : Matrix (Fin n) (Fin m) ℤ_[p], X = C * Y)
    {r : ℕ} (hr1 : 1 ≤ r) (hrk : ((4 : ℤ_[p]) * T.det).valuation < r) (hrc : C.det ∣ (p : ℤ_[p]) ^ r) :
    (countA p r (Cᵀ * S * C) T : ℝ) = ‖C.det‖⁻¹ ^ m * countA p r S T := by
  classical
  set S' := Cᵀ * S * C with hS'def
  have hS' : S'ᵀ = S' := by simp [S', transpose_mul, hS, Matrix.mul_assoc]
  have hgram : ∀ Y : Matrix (Fin n) (Fin m) ℤ_[p], (C * Y)ᵀ * S * (C * Y) = Yᵀ * S' * Y := fun Y => by
    simp only [S', transpose_mul, Matrix.mul_assoc]
  rw [countA_eq_card hS' hT, countA_eq_card hS hT]
  -- `Φ` maps `A(T, S')` into `A(T, S)`
  have hmapsto : ∀ Y, GoodA p r r S' T Y → GoodA p r r S T (phiC C r Y) := by
    intro Y hY
    rw [GoodA, phiC, modE_gram_iff_of_mcong hS hr1 (mcong_liftRes_red _), hgram]
    exact hY
  -- membership in `A(T, S')` only depends on `CY mod p^r`
  have hcong : ∀ Y Y' : Matrix (Fin n) (Fin m) (Fin (p ^ r)), phiC C r Y = phiC C r Y' →
      (GoodA p r r S' T Y ↔ GoodA p r r S' T Y') := by
    intro Y Y' hYY
    have hm : MCong p r (C * liftRes p r Y) (C * liftRes p r Y') := red_map_eq_iff.mp hYY
    simp only [GoodA]
    rw [← hgram, ← hgram]
    exact modE_gram_iff_of_mcong hS hr1 hm
  -- `Φ` is onto `A(T, S)`: a chosen preimage
  have hsurj : ∀ X : {X // GoodA p r r S T X}, ∃ Y : {Y // GoodA p r r S' T Y}, phiC C r Y.1 = X.1 := by
    rintro ⟨X, hX⟩
    obtain ⟨V, hVu, hV⟩ := exists_isometry_of_cong hS hT hdet hrk (liftRes p r X) (dvd_of_modE hX)
    obtain ⟨Y1, hY1⟩ := hfac _ hV
    have hVdet : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det V).mp hVu
    set W := Y1 * V⁻¹
    have hXW : liftRes p r X = C * W := by
      rw [show W = Y1 * V⁻¹ from rfl, ← Matrix.mul_assoc, ← hY1, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hVdet, Matrix.mul_one]
    have hphi : phiC C r (W.map (red p r)) = X := by
      rw [phiC, red_map_eq_iff.mpr ((mcong_liftRes_red W).mul_left C), ← hXW, red_map_liftRes]
    refine ⟨⟨W.map (red p r), ?_⟩, hphi⟩
    have := hmapsto
    rw [GoodA, modE_gram_iff_of_mcong hS' hr1 (mcong_liftRes_red W), ← hgram, ← hXW]
    exact hX
  choose sec hsec using hsurj
  -- the kernel
  let K := {Z : Matrix (Fin n) (Fin m) (Fin (p ^ r)) //
    ∀ i j, (p : ℤ_[p]) ^ r ∣ (C * Z.map fun a => (((a : ℕ)) : ℤ_[p])) i j}
  have hK : ∀ Z : Matrix (Fin n) (Fin m) (Fin (p ^ r)),
      (∀ i j, (p : ℤ_[p]) ^ r ∣ (C * Z.map fun a => (((a : ℕ)) : ℤ_[p])) i j) ↔
        MCong p r (C * liftRes p r Z) 0 := by
    intro Z
    rw [mcong_iff_dvd]
    simp [liftRes]
  let Φ' : {Y // GoodA p r r S' T Y} → {X // GoodA p r r S T X} := fun Y => ⟨phiC C r Y.1, hmapsto _ Y.2⟩
  -- each fiber is in bijection with the kernel
  have hfib : ∀ X : {X // GoodA p r r S T X}, Nonempty ({Y // Φ' Y = X} ≃ K) := by
    intro X
    set Y0 := (sec X).1
    have hY0 : phiC C r Y0 = X.1 := hsec X
    have hfibY : ∀ Y : {Y // Φ' Y = X}, MCong p r (C * liftRes p r Y.1.1) (C * liftRes p r Y0) := by
      intro Y
      apply red_map_eq_iff.mp
      have := congrArg Subtype.val Y.2
      change phiC C r Y.1.1 = phiC C r Y0
      rw [hY0]
      exact this
    have hph : ∀ Z : K, phiC C r ((liftRes p r Y0 + liftRes p r Z.1).map (red p r)) = phiC C r Y0 := by
      intro Z
      apply red_map_eq_iff.mpr
      have h1 := (mcong_liftRes_red (k := r) (liftRes p r Y0 + liftRes p r Z.1)).mul_left C
      refine h1.trans' ?_
      rw [Matrix.mul_add]
      have := (MCong.refl' (C * liftRes p r Y0)).add ((hK Z.1).mp Z.2)
      rwa [add_zero] at this
    refine ⟨{ toFun := fun Y => ⟨(liftRes p r Y.1.1 - liftRes p r Y0).map (red p r), ?_⟩
              invFun := fun Z => ⟨⟨(liftRes p r Y0 + liftRes p r Z.1).map (red p r), ?_⟩, ?_⟩
              left_inv := fun Y => ?_
              right_inv := fun Z => ?_ }⟩
    · rw [hK]
      have h1 := (mcong_liftRes_red (k := r) (liftRes p r Y.1.1 - liftRes p r Y0)).mul_left C
      refine h1.trans' ?_
      rw [Matrix.mul_sub]
      have := (hfibY Y).sub (MCong.refl' (C * liftRes p r Y0))
      rwa [sub_self] at this
    · exact (hcong _ _ (hph Z)).mpr (sec X).2
    · apply Subtype.ext
      change phiC C r _ = X.1
      rw [hph Z, hY0]
    · apply Subtype.ext; apply Subtype.ext
      change (liftRes p r Y0 + liftRes p r ((liftRes p r Y.1.1 - liftRes p r Y0).map (red p r))).map (red p r) =
        Y.1.1
      conv_rhs => rw [← red_map_liftRes Y.1.1]
      apply red_map_eq_iff.mpr
      have h1 := (MCong.refl' (liftRes p r Y0)).add
        (mcong_liftRes_red (k := r) (liftRes p r Y.1.1 - liftRes p r Y0))
      rwa [add_sub_cancel] at h1
    · apply Subtype.ext
      change (liftRes p r ((liftRes p r Y0 + liftRes p r Z.1).map (red p r)) - liftRes p r Y0).map (red p r) = Z.1
      conv_rhs => rw [← red_map_liftRes Z.1]
      apply red_map_eq_iff.mpr
      have h1 := (mcong_liftRes_red (k := r) (liftRes p r Y0 + liftRes p r Z.1)).sub
        (MCong.refl' (liftRes p r Y0))
      rwa [add_sub_cancel_left] at h1
  have hcard : Nat.card {Y // GoodA p r r S' T Y} = Nat.card {X // GoodA p r r S T X} * Nat.card K := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv Φ'), Nat.card_sigma,
      Finset.sum_congr rfl fun X _ => Nat.card_congr (hfib X).some, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, Nat.card_eq_fintype_card (α := {X // GoodA p r r S T X})]
  rw [hcard, Nat.cast_mul, card_ker_mat_eq C hC r m hrc, mul_comm]

/-- $\det C \mid p^r$ once $r \ge \operatorname{ord}_p\det C$. -/
theorem det_dvd_pow {C : Matrix (Fin n) (Fin n) ℤ_[p]} (hC : C.det ≠ 0) {r : ℕ} (hr : C.det.valuation ≤ r) :
    C.det ∣ (p : ℤ_[p]) ^ r := by
  have hu := PadicInt.unitCoeff_spec hC
  generalize PadicInt.unitCoeff hC = u at hu
  generalize C.det.valuation = v at hu hr
  refine ⟨(↑u⁻¹ : ℤ_[p]) * (p : ℤ_[p]) ^ (r - v), ?_⟩
  calc (p : ℤ_[p]) ^ r = (↑u * (↑u⁻¹ : ℤ_[p])) * ((p : ℤ_[p]) ^ v * (p : ℤ_[p]) ^ (r - v)) := by
        rw [Units.mul_inv, one_mul, ← pow_add, Nat.add_sub_cancel' hr]
    _ = C.det * ((↑u⁻¹ : ℤ_[p]) * (p : ℤ_[p]) ^ (r - v)) := by rw [hu]; ring

/-- **Kitaoka 1993, Theorem 5.6.4 (e)** (p. 116), *proved*: if $N' \subseteq N$ and $\eta(M) \subseteq N'$ for every
isometry $\eta : M \rightarrowtail N$, then $\beta_p(M, N) = [N : N']^{-m}\beta_p(M, N')$ (statement `Theorem564e`:
$S' = C^{\mathsf T}SC$, $[N : N'] = |\det C|_p^{-1}$). -/
@[kb "kitaoka1993" "§5.6, Thm. 5.6.4 (e), p. 116"]
theorem theorem564e : Theorem564e := by
  intro p _ m n T S C _ hT hS hC hfac
  have hS1 : Sᵀ = S := hS.1
  have hS' : (Cᵀ * S * C)ᵀ = Cᵀ * S * C := by simp [transpose_mul, hS1, Matrix.mul_assoc]
  obtain ⟨h, A, hA, hAE⟩ := exists_h hT.1 hT.2
  set r := max (h + 1) (max (((4 : ℤ_[p]) * T.det).valuation + 1) C.det.valuation) with hr
  have hr1 : h + 1 ≤ r := le_max_left _ _
  have hrk : ((4 : ℤ_[p]) * T.det).valuation < r := by omega
  have hrv : C.det.valuation ≤ r := by omega
  rw [betaP_eq hS.1 hT.1 hA hAE hr1, betaP_eq hS' hT.1 hA hAE hr1, normA, normA,
    countA_factor hS.1 hT.1 hT.2 hC hfac (by omega) hrk (det_dvd_pow hC hrv)]
  have hn : ‖C.det‖ ≠ 0 := norm_ne_zero_iff.mpr hC
  rw [mul_left_comm, ← mul_assoc (‖C.det‖ ^ m), ← mul_pow, mul_inv_cancel₀ hn, one_pow, one_mul]

end QuadFormsKB.Kitaoka.Density
