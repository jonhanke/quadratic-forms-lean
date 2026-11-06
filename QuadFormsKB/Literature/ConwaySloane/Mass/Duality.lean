/-
# Conway–Sloane 1988: invariance of the $p$-mass under dualizing, and the unimodular case of (3)

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988) (bibliography key `conwaysloane1988`), abstract, p. 259: "Our version, unlike earlier ones, is visibly invariant
under scale changes and dualizing" (scaling is `Invariance.lean`).

**Dualizing.** For a form $f$ whose symbol is supported on the scales $p^k$, $k < N$, the dual lattice rescaled by
$p^{N-1}$ has the constituent of scale $p^{N-1-k}$ equal to the dual of the constituent $f_{p^k}$ of $f$. A unit
constituent and its dual have the same dimension, sign (the determinants $\det f_q$ and $\det f_q^{-1}$ have the same
quadratic character), type, and oddity ($1/a \equiv a \pmod 8$ for odd $a$); so the symbol of the dual is the reversal
`revOdd σ N`, `revTwo σ N`. (That the symbol of the dual form is the reversed symbol is not proved here; the statements
below are about the right-hand side of (3).)
* `pMassOdd_rev`: $p$ odd; `pMassTwo_rev`: $p = 2$ (for a symbol supported below $N$). The cross-product exponent is
  symmetric under $k \mapsto N-1-k$ (`crossExp_rev`); $n(\mathrm{II})$ and $n(\mathrm{I,I})$ (adjacent type I pairs) are
  preserved; at $p = 2$ the love forms $f_{1/2}$ (`halfFactor`, bound iff $f_1$ has type I) and $f_{2^N}$ (bound iff
  $f_{2^{N-1}}$ has type I) swap roles (`diagProdTwo_rev`).

**Unimodular case of (3).** `pMassDensity_eq_pMassOdd_of_unimodular`: for an odd prime $p \nmid \det A$ and any $p$-adic
symbol $\sigma$ of $A$ (`IsOddSymbolOf`) supported below $N \ge 1$, the $p$-mass of §12 equals the right-hand side of
(3). So the named input `PMassFormulaOdd p` (`Formula.lean`) holds for all forms with $p \nmid \det A$. Proof: the
determinant of $\mathrm{diag}(p^{z_i}u_i) \sim A$ is a unit, so all $z_i = 0$ and $\sigma = 1^{\varepsilon n}$ with
$\varepsilon = \left(\frac{\det A}{p}\right)$ (`symbol_unimodular`, using `isSquare_padic_iff`); then `pMassOdd_unimodular` and
`pMassDensity_eq_stdP`.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.Main

namespace QuadFormsKB.ConwaySloane.Mass

open Finset

/-- The dual of an odd symbol supported below `N`: the constituent of scale $p^{k}$ is that of scale $p^{N-1-k}$. -/
def revOdd (σ : OddSymbol) (N : ℕ) : OddSymbol := fun k => if k < N then σ (N - 1 - k) else OddFactor.trivial

/-- The dual of a 2-adic symbol supported below `N`: the constituent of scale $2^{k}$ is that of scale $2^{N-1-k}$. -/
def revTwo (σ : TwoSymbol) (N : ℕ) : TwoSymbol := fun k => if k < N then σ (N - 1 - k) else TwoFactor.trivial

theorem crossExp_rev (d : ℕ → ℕ) (N : ℕ) :
    crossExp (fun k => if k < N then d (N - 1 - k) else 0) N = crossExp d N := by
  have hT : ∀ e : ℕ → ℕ, crossExp e N =
      ∑ a ∈ range N, ∑ b ∈ range N, if b < a then (a - b) * e b * e a else 0 := by
    intro e
    unfold crossExp
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [← Finset.sum_filter]
    have : (range N).filter (· < a) = range a := by
      ext x; simp only [mem_filter, mem_range] at *; omega
    rw [this]
  rw [hT, hT]
  rw [← Finset.sum_range_reflect (fun a => ∑ b ∈ range N, if b < a then (a - b) * d b * d a else 0) N]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← Finset.sum_range_reflect (fun b => if b < N - 1 - j then (N - 1 - j - b) * d b * d (N - 1 - j) else 0) N]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hj' := mem_range.mp hj
  have hb' := mem_range.mp hb
  simp only [if_pos hj', if_pos hb']
  by_cases h : j < b
  · rw [if_pos h, if_pos (by omega)]
    have e : N - 1 - j - (N - 1 - b) = b - j := by omega
    rw [e]; ring
  · rw [if_neg h, if_neg (by omega)]

/-- **Invariance under dualizing, $p$ odd** (Conway–Sloane 1988, abstract, p. 259): the $p$-mass (3) of the reversed
symbol equals that of $\sigma$. (No support hypothesis is needed: only scales $p^k$, $k < N$, enter.) -/
@[kb "conwaysloane1988" "abstract, p. 259 (invariance under dualizing)"]
theorem pMassOdd_rev (p : ℕ) (σ : OddSymbol) (N : ℕ) : pMassOdd p (revOdd σ N) N = pMassOdd p σ N := by
  unfold pMassOdd
  have hc : crossExp (fun k => (revOdd σ N k).dim) N = crossExp (fun k => (σ k).dim) N := by
    rw [← crossExp_rev (fun k => (σ k).dim) N]
    congr 1
    funext k
    by_cases hk : k < N <;> simp [revOdd, hk, OddFactor.trivial]
  rw [hc]
  congr 2
  rw [← Finset.prod_range_reflect (fun k => (oddSpecies p (σ k)).diagFactor p) N]
  refine Finset.prod_congr rfl fun k hk => ?_
  have : k < N := mem_range.mp hk
  simp [revOdd, this]

theorem nII_rev (σ : TwoSymbol) (N : ℕ) : nII (revTwo σ N) N = nII σ N := by
  unfold nII
  rw [← Finset.sum_range_reflect (fun k => if (σ k).type = .II then (σ k).dim else 0) N]
  refine Finset.sum_congr rfl fun k hk => ?_
  have : k < N := mem_range.mp hk
  simp [revTwo, this]

theorem nII'_rev (σ : TwoSymbol) (N : ℕ) (hσ : ∀ k, N ≤ k → σ k = TwoFactor.trivial) :
    nII' (revTwo σ N) N = nII' σ N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [nII']
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  unfold nII'
  rw [← Finset.sum_range_reflect (fun k => if (revTwo σ (M + 1) k).type = .I ∧ (revTwo σ (M + 1) (k + 1)).type = .I
    then 1 else 0) (M + 1)]
  rw [Finset.sum_range_succ', Finset.sum_range_succ]
  have h0 : (σ (M + 1)).type = .II := by rw [hσ (M + 1) le_rfl]; rfl
  have h1 : ∀ k ∈ range M, (if (revTwo σ (M + 1) (M + 1 - 1 - (k + 1))).type = .I ∧
        (revTwo σ (M + 1) (M + 1 - 1 - (k + 1) + 1)).type = .I then 1 else 0) =
      (if (σ k).type = .I ∧ (σ (k + 1)).type = .I then 1 else 0) := by
    intro k hk
    have hk' := mem_range.mp hk
    have e1 : M + 1 - 1 - (k + 1) < M + 1 := by omega
    have e2 : M + 1 - 1 - (k + 1) + 1 < M + 1 := by omega
    simp only [revTwo, if_pos e1, if_pos e2]
    have e3 : M + 1 - 1 - (M + 1 - 1 - (k + 1)) = k + 1 := by omega
    have e4 : M + 1 - 1 - (M + 1 - 1 - (k + 1) + 1) = k := by omega
    rw [e3, e4]
    exact if_congr and_comm rfl rfl
  rw [Finset.sum_congr rfl h1]
  have e5 : (if (revTwo σ (M + 1) (M + 1 - 1 - 0)).type = .I ∧ (revTwo σ (M + 1) (M + 1 - 1 - 0 + 1)).type = .I
      then 1 else 0) = 0 := by
    have : ¬ (M + 1 - 1 - 0 + 1 < M + 1) := by omega
    simp [revTwo, TwoFactor.trivial]
  rw [e5]
  simp [h0]

theorem isBound_rev {σ : TwoSymbol} {M : ℕ} (hσ : ∀ k, M + 1 ≤ k → σ k = TwoFactor.trivial) {k : ℕ}
    (hk : k < M + 1) : IsBound (revTwo σ (M + 1)) (M + 1 - 1 - k) ↔ IsBound σ k := by
  have hII : (σ (M + 1)).type = .II := by rw [hσ (M + 1) le_rfl]; rfl
  unfold IsBound revTwo
  by_cases h0 : k = 0
  · subst h0
    simp [TwoFactor.trivial]
    by_cases hM : M = 0
    · subst hM; simp [hII]
    · have : M - (M - 1) = 1 := by omega
      simp [hM, this]
  · rcases Nat.lt_or_ge k M with hkM | hkM
    · have a1 : M + 1 - 1 - k - 1 < M + 1 := by omega
      have a2 : M + 1 - 1 - k + 1 < M + 1 := by omega
      have e1 : M + 1 - 1 - (M + 1 - 1 - k - 1) = k + 1 := by omega
      have e2 : M + 1 - 1 - (M + 1 - 1 - k + 1) = k - 1 := by omega
      have a3 : M + 1 - 1 - k ≠ 0 := by omega
      rw [if_pos a1, if_pos a2, e1, e2]
      have a4 : ¬ (M - k = 0) := by omega
      simp [a4, h0]
      tauto
    · have hkM' : k = M := by omega
      subst hkM'
      have a2 : k + 1 - 1 - k + 1 < k + 1 := by omega
      have e2 : k + 1 - 1 - (k + 1 - 1 - k + 1) = k - 1 := by omega
      have a3 : ¬ (k + 1 - 1 - k ≠ 0) := by omega
      rw [if_pos a2, e2]
      simp [a3, h0, hII]

theorem trivial_diagFactor (b : Prop) [Decidable b] :
    ((twoSpecies TwoFactor.trivial b).diagFactor 2 : ℚ) = if b then 1 / 2 else 1 := by
  by_cases hb : b
  · rw [twoSpecies_trivial_bound hb, if_pos hb]
    simp (config := { decide := true }) [Species.diagFactor, Species.odd, lowerProd]
  · rw [twoSpecies_trivial_free hb, if_neg hb]
    rfl

theorem diagProdTwo_rev {σ : TwoSymbol} {M : ℕ} (hσ : ∀ k, M + 1 ≤ k → σ k = TwoFactor.trivial) :
    diagProdTwo (revTwo σ (M + 1)) (M + 1) = diagProdTwo σ (M + 1) := by
  have hσ1 : σ (M + 1) = TwoFactor.trivial := hσ _ le_rfl
  have hσ2 : σ (M + 1 + 1) = TwoFactor.trivial := hσ _ (by omega)
  have hP : ∏ k ∈ range (M + 1), (twoSpecies (revTwo σ (M + 1) k) (IsBound (revTwo σ (M + 1)) k)).diagFactor 2 =
      ∏ k ∈ range (M + 1), (twoSpecies (σ k) (IsBound σ k)).diagFactor 2 := by
    rw [← Finset.prod_range_reflect (fun k => (twoSpecies (revTwo σ (M + 1) k) (IsBound (revTwo σ (M + 1)) k)).diagFactor 2) (M + 1)]
    refine Finset.prod_congr rfl fun k hk => ?_
    have hk' : k < M + 1 := mem_range.mp hk
    have e : revTwo σ (M + 1) (M + 1 - 1 - k) = σ k := by
      simp only [revTwo, if_pos (show M + 1 - 1 - k < M + 1 by omega)]
      congr 1; omega
    rw [e, twoSpecies_congr (isBound_rev hσ hk') rfl rfl rfl]
  have hr : (revTwo σ (M + 1) (M + 1)) = TwoFactor.trivial := by simp [revTwo]
  have hr0 : revTwo σ (M + 1) 0 = σ M := by simp [revTwo]
  have hrM : revTwo σ (M + 1) M = σ 0 := by
    simp only [revTwo, if_pos (show M < M + 1 by omega)]; congr 1; omega
  have hb1 : IsBound (revTwo σ (M + 1)) (M + 1) ↔ (σ 0).type = .I := by
    unfold IsBound
    simp only [Nat.add_sub_cancel]
    rw [hrM, show revTwo σ (M + 1) (M + 1 + 1) = TwoFactor.trivial by simp [revTwo]]
    simp [TwoFactor.trivial]
  have hb2 : IsBound σ (M + 1) ↔ (σ M).type = .I := by
    unfold IsBound
    rw [hσ2]
    simp [TwoFactor.trivial]
  unfold diagProdTwo
  rw [Finset.prod_range_succ _ (M + 1), Finset.prod_range_succ _ (M + 1), hP, hr, hσ1, trivial_diagFactor, trivial_diagFactor]
  unfold halfFactor
  rw [hr0]
  simp only [if_congr hb1 rfl rfl, if_congr hb2 rfl rfl]
  ring

/-- **Invariance under dualizing, $p = 2$** (Conway–Sloane 1988, abstract, p. 259): for a 2-adic symbol supported below
$N$, the 2-mass (3) of the reversed symbol equals that of $\sigma$. -/
@[kb "conwaysloane1988" "abstract, p. 259 (invariance under dualizing)"]
theorem pMassTwo_rev {σ : TwoSymbol} {N : ℕ} (hσ : ∀ k, N ≤ k → σ k = TwoFactor.trivial) :
    pMassTwo (revTwo σ N) N = pMassTwo σ N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have : revTwo σ 0 = σ := by
      funext k; simp [revTwo, hσ k (Nat.zero_le k)]
    rw [this]
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hc : crossExp (fun k => ((revTwo σ (M + 1)) k).dim) (M + 1) = crossExp (fun k => (σ k).dim) (M + 1) := by
    rw [← crossExp_rev (fun k => (σ k).dim) (M + 1)]
    congr 1
    funext k
    by_cases hk : k < M + 1 <;> simp [revTwo, hk, TwoFactor.trivial]
  unfold pMassTwo
  rw [diagProdTwo_rev hσ, hc, nII_rev, nII'_rev σ (M + 1) hσ]

/-! ### (b) The unimodular case at an odd prime -/

section Unimodular

variable {p : ℕ} [hp : Fact p.Prime]

theorem isSquare_padic_iff (hp2 : p ≠ 2) {d : ℤ} (hd : ¬ (p : ℤ) ∣ d) :
    IsSquare (d : ℚ_[p]) ↔ jacobiSym d p = 1 := by
  constructor
  · rintro ⟨x, hx⟩
    have hdn : ‖(d : ℚ_[p])‖ = 1 :=
      le_antisymm (Padic.norm_int_le_one d)
        (not_lt.mp fun h => hd ((PadicInt.norm_int_lt_one_iff_dvd d).mp (by simpa using h)))
    have hn : ‖x‖ = 1 := by
      rw [hx, norm_mul] at hdn
      nlinarith [norm_nonneg x]
    let y : ℤ_[p] := ⟨x, (PadicInt.mem_subring_iff p).2 hn.le⟩
    have hy : (d : ℤ_[p]) = y * y := Subtype.ext (by simpa using hx)
    have hz : ((d : ℤ) : ZMod p) ≠ 0 := fun h => hd ((ZMod.intCast_zmod_eq_zero_iff_dvd d p).mp h)
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_one_iff p hz]
    refine ⟨PadicInt.toZMod y, ?_⟩
    have := congrArg PadicInt.toZMod hy
    rwa [map_intCast, map_mul] at this
  · intro hJ
    obtain ⟨z, hz⟩ := Binary.exists_sq_padic_odd hp2 hd hJ
    refine ⟨(z : ℚ_[p]), ?_⟩
    have := congrArg (fun w : ℤ_[p] => (w : ℚ_[p])) hz
    simpa [sq] using this.symm

/-- The $p$-adic symbol of a unimodular form ($p \nmid \det A$, $p$ odd) is $1^{\varepsilon n}$,
$\varepsilon = \left(\frac{\det A}{p}\right)$. -/
@[kb "conwaysloane1988" "(3), p. 263; §7, p. 266 (unimodular case)"]
theorem symbol_unimodular (hp2 : p ≠ 2) {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ} (hpd : ¬ (p : ℤ) ∣ A.det)
    {σ : OddSymbol} (hσ : IsOddSymbolOf p (A.map (Int.cast : ℤ → ℚ_[p])) σ) :
    σ = unimodularSymbol n (Sign.ofInt (jacobiSym A.det p)) := by
  obtain ⟨z, u, hu, ⟨T, hT⟩, rfl⟩ := hσ
  have hdetF : (A.map (Int.cast : ℤ → ℚ_[p])).det = (A.det : ℚ_[p]) := by
    have := (RingHom.map_det (Int.castRingHom ℚ_[p]) A).symm
    simpa using this
  have hFn : ‖(A.det : ℚ_[p])‖ = 1 :=
    le_antisymm (Padic.norm_int_le_one _)
      (not_lt.mp fun h => hpd ((PadicInt.norm_int_lt_one_iff_dvd A.det).mp (by simpa using h)))
  set dT : ℚ_[p] := (T.val.map PadicInt.Coe.ringHom).det with hdT
  have hdTn : ‖dT‖ = 1 := by
    have h1 : dT = ((T.val.det : ℤ_[p]) : ℚ_[p]) := by
      rw [hdT]
      exact (RingHom.map_det PadicInt.Coe.ringHom T.val).symm
    have h2 : IsUnit T.val.det := (Matrix.isUnit_iff_isUnit_det _).mp T.isUnit
    rw [h1]
    exact PadicInt.isUnit_iff.mp h2
  have hdet : (Matrix.diagonal fun i => (p : ℚ_[p]) ^ (z i) * u i).det = dT ^ 2 * (A.det : ℚ_[p]) := by
    rw [← hT, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdetF]
    ring
  have hnorm : ‖(Matrix.diagonal fun i => (p : ℚ_[p]) ^ (z i) * u i).det‖ = 1 := by
    rw [hdet, norm_mul, norm_pow, hdTn, hFn]; simp
  rw [Matrix.det_diagonal, norm_prod] at hnorm
  have hprod : ∀ i, ‖(p : ℚ_[p]) ^ (z i) * u i‖ = ‖(p : ℚ_[p])‖ ^ (z i) := fun i => by
    rw [norm_mul, hu i, mul_one, norm_pow]
  simp only [hprod, Finset.prod_pow_eq_pow_sum] at hnorm
  have hsum : ∑ i, z i = 0 := by
    by_contra hne
    have : ‖(p : ℚ_[p])‖ ^ (∑ i, z i) < 1 := pow_lt_one₀ (norm_nonneg _) Padic.norm_p_lt_one hne
    linarith
  have hz : ∀ i, z i = 0 := fun i => (Finset.sum_eq_zero_iff.mp hsum) i (Finset.mem_univ i)
  have hsq : IsSquare (∏ i : Fin n, u i) ↔ IsSquare (A.det : ℚ_[p]) := by
    have h1 : (∏ i : Fin n, u i) = dT ^ 2 * (A.det : ℚ_[p]) := by
      rw [← hdet, Matrix.det_diagonal]
      exact Finset.prod_congr rfl fun i _ => by rw [hz i]; simp
    have hdT0 : dT ≠ 0 := norm_pos_iff.mp (by rw [hdTn]; exact one_pos)
    exact isSquare_iff_of_eq hdT0 h1
  funext k
  unfold oddSymbolOfDiag unimodularSymbol
  by_cases hk : k = 0
  · subst hk
    let e : {i : Fin n // z i = 0} ≃ Fin n := Equiv.subtypeUnivEquiv fun i => hz i
    have hc : Fintype.card {i : Fin n // z i = 0} = n := by
      rw [Fintype.card_congr e, Fintype.card_fin]
    have hP : (∏ i : {i : Fin n // z i = 0}, u i) = ∏ i : Fin n, u i :=
      Fintype.prod_equiv e _ _ (fun _ => rfl)
    have hJ := isSquare_padic_iff hp2 hpd
    have hJ' : jacobiSym A.det p = 1 ∨ jacobiSym A.det p = -1 := by
      have hcop : Nat.Coprime p A.det.natAbs :=
        (Nat.Prime.coprime_iff_not_dvd hp.out).mpr fun h => hpd (Int.natCast_dvd.mpr h)
      exact jacobiSym.eq_one_or_neg_one (by simpa [Int.gcd] using hcop.symm)
    simp only [if_true]
    rw [hc, hP]
    congr 1
    by_cases hs : IsSquare (∏ i : Fin n, u i)
    · rw [if_pos hs, (hJ.mp (hsq.mp hs))]; rfl
    · rw [if_neg hs]
      have : jacobiSym A.det p = -1 := by
        rcases hJ' with h | h
        · exact absurd (hsq.mpr (hJ.mpr h)) hs
        · exact h
      rw [this]; rfl
  · simp only [if_neg hk]
    have hc : Fintype.card {i : Fin n // z i = k} = 0 := by
      rw [Fintype.card_eq_zero_iff]
      exact ⟨fun ⟨i, hi⟩ => hk (by rw [← hi, hz i])⟩
    have hemp : IsEmpty {i : Fin n // z i = k} := Fintype.card_eq_zero_iff.mp hc
    simp [OddFactor.trivial, hc]

/-- **The unimodular case of (3) at an odd prime** (Conway–Sloane 1988, (3), p. 263; §7, p. 266): for an odd prime
$p \nmid \det A$ ($A$ symmetric, $n \ge 1$) and a $p$-adic symbol $\sigma$ of $A$ supported below $N \ge 1$,
`pMassDensity p A = pMassOdd p σ N`. -/
@[kb "conwaysloane1988" "(3), p. 263; §7, p. 266 (unimodular case)"]
theorem pMassDensity_eq_pMassOdd_of_unimodular (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n)
    {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.IsSymm) (hpd : ¬ (p : ℤ) ∣ A.det) {σ : OddSymbol} {N : ℕ}
    (hN1 : 1 ≤ N) (hσ : IsOddSymbolOf p (A.map (Int.cast : ℤ → ℚ_[p])) σ)
    (_hsupp : ∀ k, N ≤ k → σ k = OddFactor.trivial) : pMassDensity p A = pMassOdd p σ N := by
  have hdet : A.det ≠ 0 := fun h => hpd (by rw [h]; exact dvd_zero _)
  have hs := symbol_unimodular hp2 hpd hσ
  subst hs
  rw [pMassOdd_congr p (fun k hk => by simp [unimodularSymbol, show k ≠ 0 by omega]) hN1,
    pMassOdd_unimodular hp2 hn hpd, pMassDensity_eq_stdP hp.out hp2 hn hA hdet hpd]

end Unimodular

end QuadFormsKB.ConwaySloane.Mass
