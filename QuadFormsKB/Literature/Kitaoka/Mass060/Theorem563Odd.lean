/-
# Kitaoka 1993, Theorem 5.6.3 (I) for odd $p$, from the Conway–Sloane $p$-mass formula

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §5.6, Theorem 5.6.3 (I), p. 108 (statement
`Kitaoka.Density.Theorem563odd`, `Wave3/Ch5Theorem563.lean`); J. H. Conway and N. J. A. Sloane, *Low-dimensional
lattices. IV. The mass formula*, Proc. Roy. Soc. London A 419 (1988), (3) and Table 1 (the $p$-mass of an odd $p$-adic
symbol, proved in the library as `ConwaySloane.Mass.pMassFormulaOdd`).

**Route (a bridge, not a re-proof).** For $p$ odd and $S = \operatorname{diag}(p^{e_i}u_i)$:
1. replace the units $u_i$ by integers $a_i \equiv u_i \bmod p$; then $u_i = c_i^2a_i$ with $c_i \in \mathbb Z_p^\times$
   (Hensel, `HilbertLocal.isSquare_unit_iff`), so $\beta_p(S, S) = \beta_p(A, A)$ for the integer matrix
   $A = \operatorname{diag}(p^{e_i}a_i)$ (`Kitaoka.Density.betaP_conj`);
2. for $p$ odd Kitaoka's count $\#A_{p^r}(A, A)$ is the Conway–Sloane count $N(p^r)$ and the normalizations agree,
   so $\beta_p(A, A) = \alpha_p(A)$ (Conway–Sloane's density) (`betaP_map_eq_alphaP`);
3. $\alpha_p(A) = p^{s(n+1)/2}/m_p(A)$ by definition of the $p$-mass, and $m_p(A)$ is the Conway–Sloane product
   (`pMassFormulaOdd`);
4. the Conway–Sloane product equals Kitaoka's $2^sp^wPE$: the exponent identity
   $2w + \sum_{j<k}(k - j)n_jn_k = s(n+1)$ with $s = \sum_j jn_j$, and per Jordan component
   $M_p(\text{species})^{-1} = 2P([n_j/2])(1 + \chi(N_j)p^{-n_j/2})^{-1}$ (the sign rule of Table 1 matches
   $\chi(N_j) = \chi_p((-1)^{n_j/2}\prod u_i)$).

**Proves** (unconditional; standard axioms only) `theorem563odd_holds : Theorem563odd`.
-/
import QuadFormsKB.Literature.Kitaoka.Wave3.Ch5Theorem563
import QuadFormsKB.Literature.Kitaoka.Wave2.Ch5Invariance
import QuadFormsKB.Literature.ConwaySloane.Mass.OddProof
import QuadFormsKB.Literature.LocalGlobal.HilbertLocal
import QuadFormsKB.Citation

open Matrix Filter Finset

noncomputable section

namespace QuadFormsKB.Kitaoka.Density

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Step 2: Kitaoka's count is the Conway–Sloane count ($p$ odd) -/

theorem two_isUnit (hp2 : p ≠ 2) : IsUnit (2 : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff]
  have : ‖((2 : ℕ) : ℤ_[p])‖ = 1 := by
    rw [PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.coprime_primes hp.out Nat.prime_two).2 hp2
  simpa using this

/-- An integer is divisible by $p^r$ in $\mathbb Z_p$ iff it is in $\mathbb Z$. -/
theorem intCast_dvd_iff (r : ℕ) (z : ℤ) : (p : ℤ_[p]) ^ r ∣ (z : ℤ_[p]) ↔ (p : ℤ) ^ r ∣ z := by
  constructor
  · intro h
    have h1 := map_dvd (PadicInt.toZModPow r) h
    rw [map_pow, map_natCast, map_intCast] at h1
    have h0 : ((p : ZMod (p ^ r)) ^ r) = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_self]
    rw [h0, zero_dvd_iff] at h1
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd z (p ^ r)).1 h1
    exact_mod_cast this
  · rintro ⟨c, rfl⟩
    exact ⟨c, by push_cast; ring⟩

theorem countA_map_eq_countN (hp2 : p ≠ 2) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (r : ℕ) :
    countA p r (A.map (Int.castRingHom ℤ_[p])) (A.map (Int.castRingHom ℤ_[p])) =
      ConwaySloane.Mass.countN p r A := by
  have hpr : NeZero (p ^ r) := ⟨pow_ne_zero r hp.out.ne_zero⟩
  let e : Fin (p ^ r) ≃ ZMod (p ^ r) :=
    { toFun := fun a => ((a : ℕ) : ZMod (p ^ r))
      invFun := fun z => ⟨z.val, ZMod.val_lt z⟩
      left_inv := fun a => Fin.ext (ZMod.val_cast_of_lt a.2)
      right_inv := fun z => ZMod.natCast_zmod_val z }
  unfold countA ConwaySloane.Mass.countN
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.mapMatrix e) fun X => ?_)
  -- the integer matrix of residues
  let Xz : Matrix (Fin n) (Fin n) ℤ := X.map fun a => ((a : ℕ) : ℤ)
  have hlift : liftRes p r X = Xz.map (Int.castRingHom ℤ_[p]) := by
    ext i j; simp [liftRes, Xz]
  have hmapZ : (Equiv.mapMatrix e X) = Xz.map (Int.castRingHom (ZMod (p ^ r))) := by
    ext i j
    simp [Xz, e]
  rw [hlift, hmapZ]
  let M : Matrix (Fin n) (Fin n) ℤ := Xzᵀ * A * Xz - A
  have hM1 : ((Xz.map (Int.castRingHom ℤ_[p]))ᵀ * A.map (Int.castRingHom ℤ_[p]) * Xz.map (Int.castRingHom ℤ_[p]) -
      A.map (Int.castRingHom ℤ_[p])) = M.map (Int.castRingHom ℤ_[p]) := by
    simp only [M]
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  have hM2 : (Xz.map (Int.castRingHom (ZMod (p ^ r))))ᵀ * A.map (Int.castRingHom (ZMod (p ^ r))) *
      Xz.map (Int.castRingHom (ZMod (p ^ r))) = A.map (Int.castRingHom (ZMod (p ^ r))) ↔
      M.map (Int.castRingHom (ZMod (p ^ r))) = 0 := by
    rw [← sub_eq_zero]
    simp only [M]
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  rw [hM1, hM2]
  constructor
  · intro h
    ext i j
    have h1 := h i j
    simp only [Matrix.map_apply, eq_intCast] at h1 ⊢
    have h2 : (p : ℤ_[p]) ^ r ∣ (M i j : ℤ_[p]) := dvd_trans (Dvd.intro _ rfl) h1
    rw [intCast_dvd_iff] at h2
    rw [Matrix.zero_apply, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast h2
  · intro h i j
    have h1 := congrFun (congrFun h i) j
    simp only [Matrix.map_apply, eq_intCast, Matrix.zero_apply] at h1 ⊢
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
    have h2 : (p : ℤ_[p]) ^ r ∣ (M i j : ℤ_[p]) := (intCast_dvd_iff r _).2 (by exact_mod_cast h1)
    split_ifs
    · obtain ⟨c, hc⟩ := h2
      obtain ⟨t, ht⟩ := (two_isUnit hp2).exists_right_inv
      exact ⟨c * t, by rw [hc]; linear_combination (↑p ^ r * c) * ht.symm⟩
    · simpa using h2

theorem natDiv_succ (n : ℕ) : n * (n + 1) / 2 = n * (n - 1) / 2 + n := by
  rcases n with _ | n
  · simp
  · have : (n + 1) * (n + 1 + 1) = (n + 1) * (n + 1 - 1) + 2 * (n + 1) := by
      rw [Nat.add_sub_cancel]; ring
    rw [this, Nat.add_mul_div_left _ _ two_pos]

/-- **Kitaoka's $\beta_p(A, A)$ is the Conway–Sloane density $\alpha_p(A)$** for $p$ odd and an integer matrix
$A$ (the two counts agree and so do the normalizations $p^{-r\,n(n-1)/2}$). -/
theorem betaP_map_eq_alphaP (hp2 : p ≠ 2) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    betaP p (A.map (Int.castRingHom ℤ_[p])) (A.map (Int.castRingHom ℤ_[p])) = ConwaySloane.Mass.alphaP p A := by
  unfold betaP ConwaySloane.Mass.alphaP
  congr 1
  funext r
  rw [countA_map_eq_countN hp2, div_eq_mul_inv, mul_comm ((ConwaySloane.Mass.countN p r A : ℕ) : ℝ)]
  congr 1
  set k := n * (n - 1) / 2 with hkdef
  have hk : 2 * k + n = n * n := by
    have h2 : 2 ∣ n * (n - 1) := (Nat.even_mul_pred_self n).two_dvd
    rcases n with _ | n
    · simp [hkdef]
    · rw [hkdef, Nat.mul_div_cancel' h2, Nat.add_sub_cancel]; ring
  have hE : (((n * (n + 1) / 2 : ℕ) : ℤ) - (n : ℤ) * n) = -(k : ℤ) := by
    rw [natDiv_succ, ← hkdef]
    have : ((n : ℤ) * n) = ((n * n : ℕ) : ℤ) := by push_cast; ring
    rw [this, ← hk]; push_cast; ring
  rw [hE, _root_.zpow_neg, zpow_natCast, ← pow_mul]

/-! ### Step 1: integer representatives of the units -/

/-- For $p$ odd and units $u, a \in \mathbb Z_p$ with the same residue modulo $p$, $u = c^2a$ for a unit $c$
(Hensel's lemma, through `HilbertLocal.isSquare_unit_iff`). -/
theorem exists_unit_sq_mul (hp2 : p ≠ 2) {u a : ℤ_[p]} (hu : IsUnit u) (ha : IsUnit a)
    (hua : PadicInt.toZMod u = PadicInt.toZMod a) : ∃ c : ℤ_[p], IsUnit c ∧ c * c * a = u := by
  let x : ℤ_[p]ˣ := hu.unit * ha.unit⁻¹
  have hx1 : PadicInt.toZMod (x : ℤ_[p]) = 1 := by
    have hxa : (x : ℤ_[p]) * a = u := by
      simp only [x, Units.val_mul, IsUnit.unit_spec]
      rw [mul_assoc, IsUnit.val_inv_mul, mul_one]
    have h1 : PadicInt.toZMod (x : ℤ_[p]) * PadicInt.toZMod a = PadicInt.toZMod a := by
      rw [← map_mul, hxa, hua]
    have h2 : PadicInt.toZMod a ≠ 0 := by
      intro h0
      have : a ∈ RingHom.ker (PadicInt.toZMod : ℤ_[p] →+* ZMod p) := h0
      rw [PadicInt.ker_toZMod] at this
      exact (IsLocalRing.mem_maximalIdeal _).1 this ha
    exact mul_right_cancel₀ h2 (by rw [h1, one_mul])
  have hsq : IsSquare ((x : ℤ_[p]) : ℚ_[p]) := by
    rw [HilbertLocal.isSquare_unit_iff hp2, hx1]
    exact ⟨1, (one_mul 1).symm⟩
  obtain ⟨r, hr⟩ := hsq
  have hxn : ‖((x : ℤ_[p]) : ℚ_[p])‖ = 1 := by
    rw [PadicInt.norm_coe]; exact (PadicInt.isUnit_iff).1 x.isUnit
  have hrn : ‖r‖ = 1 := by
    rw [hr, norm_mul] at hxn
    nlinarith [norm_nonneg r]
  let c : ℤ_[p] := ⟨r, hrn.le⟩
  refine ⟨c, (PadicInt.isUnit_iff).2 hrn, ?_⟩
  have hcc : c * c = (x : ℤ_[p]) := by
    apply Subtype.ext
    change r * r = ((x : ℤ_[p]) : ℚ_[p])
    exact hr.symm
  rw [hcc]
  simp only [x, Units.val_mul, IsUnit.unit_spec]
  rw [mul_assoc, IsUnit.val_inv_mul, mul_one]

/-! ### Step 4a: the exponent identity -/

theorem crossExp_succ (d : ℕ → ℕ) (N : ℕ) :
    ConwaySloane.Mass.crossExp d (N + 1) =
      ConwaySloane.Mass.crossExp d N + ∑ k ∈ range N, (N - k) * d k * d N := by
  rw [ConwaySloane.Mass.crossExp, sum_range_succ]; rfl

/-- **The exponent identity** (for any $d : \mathbb N \to \mathbb N$ and $N$):
$\sum_{j<N}\bigl(2jd_j\sum_{j<k<N}d_k + jd_j(d_j+1)\bigr) + \sum_{k<k'<N}(k'-k)d_kd_{k'}
= \bigl(\sum_{j<N}jd_j\bigr)\bigl(\sum_{j<N}d_j + 1\bigr)$. -/
theorem exponent_identity (d : ℕ → ℕ) (N : ℕ) :
    (∑ j ∈ range N, (2 * j * d j * ∑ k ∈ Ico (j + 1) N, d k + j * (d j * (d j + 1)))) +
      ConwaySloane.Mass.crossExp d N =
    (∑ j ∈ range N, j * d j) * ((∑ j ∈ range N, d j) + 1) := by
  induction N with
  | zero => simp [ConwaySloane.Mass.crossExp]
  | succ N ih =>
    have hIco : ∀ j ∈ range N, ∑ k ∈ Ico (j + 1) (N + 1), d k = ∑ k ∈ Ico (j + 1) N, d k + d N := by
      intro j hj
      exact sum_Ico_succ_top (by simpa using hj) d
    have hW : ∑ j ∈ range (N + 1), (2 * j * d j * ∑ k ∈ Ico (j + 1) (N + 1), d k + j * (d j * (d j + 1))) =
        ∑ j ∈ range N, (2 * j * d j * ∑ k ∈ Ico (j + 1) N, d k + j * (d j * (d j + 1))) +
          2 * d N * ∑ j ∈ range N, j * d j + N * (d N * (d N + 1)) := by
      rw [sum_range_succ, Ico_self, sum_empty, mul_zero, zero_add]
      rw [sum_congr rfl fun j hj => by rw [hIco j hj]]
      have e : ∀ j, 2 * j * d j * (∑ k ∈ Ico (j + 1) N, d k + d N) + j * (d j * (d j + 1)) =
          (2 * j * d j * ∑ k ∈ Ico (j + 1) N, d k + j * (d j * (d j + 1))) + 2 * d N * (j * d j) :=
        fun j => by ring
      rw [sum_congr rfl fun j _ => e j, sum_add_distrib, ← mul_sum]
    have hC : ∑ k ∈ range N, (N - k) * d k * d N + d N * ∑ k ∈ range N, k * d k =
        N * d N * ∑ k ∈ range N, d k := by
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun k hk => ?_
      have hkN : k ≤ N := (mem_range.1 hk).le
      have : (N - k) * d k * d N + d N * (k * d k) = (N - k + k) * d k * d N := by ring
      rw [this, Nat.sub_add_cancel hkN]; ring
    rw [hW, crossExp_succ, sum_range_succ, sum_range_succ]
    zify at ih hC ⊢
    linear_combination ih + hC

/-! ### Step 4b: one Jordan component -/

open QuadFormsKB.ConwaySloane QuadFormsKB.ConwaySloane.Mass in
theorem lowerProd_eq_kitP (m : ℕ) : ((lowerProd (p : ℚ) m : ℚ) : ℝ) = kitP p m := by
  induction m with
  | zero => simp [lowerProd, kitP]
  | succ m ih =>
    rw [lowerProd, prod_range_succ, ← lowerProd, kitP, prod_Icc_succ_top (by omega), ← kitP]
    push_cast
    rw [ih, _root_.zpow_neg, ← zpow_natCast]
    push_cast
    ring_nf

theorem one_add_ne_zero_of_sign (hp2 : p ≠ 2) {s : ℝ} (hs : s = 1 ∨ s = -1) {t : ℕ} (ht : t ≠ 0) :
    1 + s * ((p : ℝ) ^ t)⁻¹ ≠ 0 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hq : ((p : ℝ) ^ t)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hp1 ht)
  have hq0 : 0 < ((p : ℝ) ^ t)⁻¹ := by positivity
  rcases hs with rfl | rfl <;> intro h <;> linarith

open QuadFormsKB.ConwaySloane QuadFormsKB.ConwaySloane.Mass in
/-- **One Jordan component**: $M_p(\text{species})^{-1} = 2P([d/2])(1 + \chi p^{-d/2})^{-1}$, where $\chi = 0$
for $d$ odd and $\chi$ is the sign of the species for $d$ even. -/
theorem inv_diagFactor_eq (hp2 : p ≠ 2) (f : OddFactor) (hd : f.dim ≠ 0) (χ : ℝ)
    (hχodd : Odd f.dim → χ = 0) (hχev : ¬ Odd f.dim → χ = ((oddSpecies p f).sign.toInt : ℝ)) :
    (((oddSpecies p f).diagFactor p : ℚ) : ℝ)⁻¹ =
      2 * kitP p (f.dim / 2) * (1 + χ * (p : ℝ) ^ (-((f.dim : ℝ) / 2)))⁻¹ := by
  have hdim : (oddSpecies p f).dim = f.dim := rfl
  by_cases hodd : Odd f.dim
  · rw [hχodd hodd, zero_mul, add_zero, inv_one, mul_one]
    rw [Species.diagFactor, hdim, if_neg hd, if_pos hodd]
    push_cast
    rw [inv_inv, lowerProd_eq_kitP]
  · obtain ⟨t, ht⟩ : ∃ t, f.dim = 2 * t := ⟨f.dim / 2, by
      have := Nat.even_iff.1 (Nat.not_odd_iff_even.1 hodd); omega⟩
    obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
    have hpow : (p : ℝ) ^ (-((f.dim : ℝ) / 2)) = ((p : ℝ) ^ (m + 1))⁻¹ := by
      rw [ht, Real.rpow_neg (by positivity)]
      congr 1
      rw [show ((2 * (m + 1) : ℕ) : ℝ) / 2 = ((m + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [hpow, hχev hodd]
    rw [Species.diagFactor, hdim, if_neg hd, if_neg hodd]
    push_cast
    rw [inv_inv, lowerProd_eq_kitP, ht, show 2 * (m + 1) / 2 = m + 1 by omega, show m + 1 - 1 = m by omega]
    have hk : kitP p (m + 1) = kitP p m * (1 - (((p : ℝ) ^ (m + 1))⁻¹) ^ 2) := by
      rw [kitP, prod_Icc_succ_top (by omega), ← kitP]
      congr 2
      rw [_root_.zpow_neg, show (2 * ((m + 1 : ℕ) : ℤ)) = ((2 * (m + 1) : ℕ) : ℤ) by push_cast; ring,
        zpow_natCast, pow_mul', inv_pow]
    rw [hk]
    have hs : ((oddSpecies p f).sign.toInt : ℝ) = 1 ∨ ((oddSpecies p f).sign.toInt : ℝ) = -1 := by
      cases (oddSpecies p f).sign <;> simp [Sign.toInt]
    generalize ((oddSpecies p f).sign.toInt : ℝ) = s at hs ⊢
    have hne := one_add_ne_zero_of_sign hp2 hs (t := m + 1) (by omega)
    have hs2 : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
    generalize ((p : ℝ) ^ (m + 1))⁻¹ = q at hne ⊢
    rw [eq_mul_inv_iff_mul_eq₀ hne]
    linear_combination (-2 * kitP p m * q ^ 2) * hs2

/-! ### Step 4c: the sign rule of Table 1 and $\chi(N_j)$ -/

theorem card_subtype_eq_jordanRank {n : ℕ} (e : Fin n → ℕ) (j : ℕ) :
    Fintype.card {i // e i = j} = jordanRank e j := by
  rw [Fintype.card_subtype]; rfl

open QuadFormsKB.ConwaySloane QuadFormsKB.ConwaySloane.Mass in
/-- **The sign rule** (Conway–Sloane Table 1 against Kitaoka's $\chi(N_j)$): for an even, nonzero rank
$d_j$, the sign of the species of the $j$-th constituent of $\operatorname{diag}(p^{e_i}a_i)$ is
$\chi_p\bigl((-1)^{d_j/2}\prod_{e_i = j}u_i\bigr)$ when $a_i \equiv u_i \bmod p$. -/
theorem sign_eq_chiJ (hp2 : p ≠ 2) {n : ℕ} (e : Fin n → ℕ) (u : Fin n → ℤ_[p]) (hu : ∀ i, IsUnit (u i))
    (a : Fin n → ℤ) (hres : ∀ i, PadicInt.toZMod ((a i : ℤ) : ℤ_[p]) = PadicInt.toZMod (u i))
    (ha : ∀ i, IsUnit ((a i : ℤ) : ℤ_[p])) (j : ℕ) (hev : ¬ Odd (jordanRank e j)) (hd : jordanRank e j ≠ 0) :
    (((oddSpecies p (oddSymbolOfDiag p e (fun i => (((a i : ℤ) : ℤ_[p]) : ℚ_[p])) j)).sign.toInt : ℤ) : ℝ) =
      chiJ p e u j := by
  classical
  set d := jordanRank e j with hddef
  obtain ⟨t, ht⟩ : ∃ t, d = 2 * t := ⟨d / 2, by
    have := Nat.even_iff.1 (Nat.not_odd_iff_even.1 hev); omega⟩
  -- the residue `y` of the product of the units
  set P : Finset (Fin n) := univ.filter fun i => e i = j with hPdef
  have hPu : IsUnit (∏ i ∈ P, ((a i : ℤ) : ℤ_[p])) :=
    ⟨∏ i ∈ P, (ha i).unit, by rw [Units.coe_prod]; exact prod_congr rfl fun i _ => (ha i).unit_spec⟩
  set y : ZMod p := PadicInt.toZMod (∏ i ∈ P, u i) with hydef
  have hy' : y = PadicInt.toZMod (∏ i ∈ P, ((a i : ℤ) : ℤ_[p])) := by
    rw [hydef, map_prod, map_prod]
    exact prod_congr rfl fun i _ => (hres i).symm
  have hy0 : y ≠ 0 := by
    rw [hy']
    intro h0
    have : (∏ i ∈ P, ((a i : ℤ) : ℤ_[p])) ∈ RingHom.ker (PadicInt.toZMod : ℤ_[p] →+* ZMod p) := h0
    rw [PadicInt.ker_toZMod] at this
    exact (IsLocalRing.mem_maximalIdeal _).1 this hPu
  -- `IsSquare` of the rational product iff `IsSquare y`
  have hsq : IsSquare (∏ i : {i // e i = j}, (((a i : ℤ) : ℤ_[p]) : ℚ_[p])) ↔ IsSquare y := by
    have h1 : (∏ i : {i // e i = j}, (((a i : ℤ) : ℤ_[p]) : ℚ_[p])) =
        ((hPu.unit : ℤ_[p]ˣ) : ℤ_[p]) := by
      rw [IsUnit.unit_spec]
      rw [show (((∏ i ∈ P, ((a i : ℤ) : ℤ_[p]) : ℤ_[p]) : ℚ_[p])) =
        PadicInt.Coe.ringHom (∏ i ∈ P, ((a i : ℤ) : ℤ_[p])) from rfl, map_prod]
      rw [Finset.prod_subtype P (p := fun i => e i = j) (fun i => by simp [P])]
      rfl
    rw [h1, HilbertLocal.isSquare_unit_iff hp2, IsUnit.unit_spec, ← hy']
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by
    rcases hp.out.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  have hχm : (quadraticChar (ZMod p) (-1) : ℤ) = if p % 4 = 1 then 1 else -1 := by
    rw [quadraticChar_neg_one hchar, ZMod.card]
    rcases hp4 with h4 | h4
    · rw [ZMod.χ₄_nat_one_mod_four h4, if_pos h4]
    · rw [ZMod.χ₄_nat_three_mod_four h4, if_neg (by omega)]
  rw [chiJ, if_neg hev]
  have hmap : PadicInt.toZMod ((-1) ^ (jordanRank e j / 2) * ∏ i ∈ univ.filter (fun i => e i = j), u i) =
      (-1) ^ t * y := by
    rw [map_mul, map_pow, map_neg, map_one, ← hddef, ht, show 2 * t / 2 = t by omega]
  rw [hmap, map_mul, map_pow, hχm]
  simp only [oddSpecies, oddSymbolOfDiag, card_subtype_eq_jordanRank, ← hddef]
  rw [if_neg (by rw [not_or]; exact ⟨hd, hev⟩)]
  have hχy : (quadraticChar (ZMod p) y : ℤ) = if IsSquare y then 1 else -1 := by
    split_ifs with hs
    · exact (quadraticChar_one_iff_isSquare hy0).2 hs
    · exact quadraticChar_neg_one_iff_not_isSquare.2 hs
  rw [hχy]
  rcases Nat.even_or_odd t with hte | hto
  · have h4 : ¬ (d % 4 = 2 ∧ p % 4 = 3) := by
      obtain ⟨r, hr⟩ := hte; omega
    rw [if_neg h4]
    have h1 : ((if p % 4 = 1 then (1 : ℤ) else -1)) ^ t = 1 := by
      split_ifs
      · exact one_pow t
      · exact hte.neg_one_pow
    rw [h1, one_mul]
    by_cases hs : IsSquare y
    · rw [if_pos (hsq.2 hs), if_pos hs]; rfl
    · rw [if_neg (fun h => hs (hsq.1 h)), if_neg hs]; rfl
  · have h1 : ((if p % 4 = 1 then (1 : ℤ) else -1)) ^ t = if p % 4 = 1 then 1 else -1 := by
      split_ifs
      · exact one_pow t
      · exact hto.neg_one_pow
    rw [h1]
    rcases hp4 with h4 | h4
    · rw [if_neg (show ¬ (d % 4 = 2 ∧ p % 4 = 3) by omega), if_pos h4, one_mul]
      by_cases hs : IsSquare y
      · rw [if_pos (hsq.2 hs), if_pos hs]; rfl
      · rw [if_neg (fun h => hs (hsq.1 h)), if_neg hs]; rfl
    · have hd4 : d % 4 = 2 ∧ p % 4 = 3 := by obtain ⟨r, hr⟩ := hto; omega
      rw [if_pos hd4, if_neg (show ¬ (p % 4 = 1) by omega)]
      by_cases hs : IsSquare y
      · rw [if_pos (hsq.2 hs), if_pos hs]; rfl
      · rw [if_neg (fun h => hs (hsq.1 h)), if_neg hs]; rfl

/-! ### Step 4d: Kitaoka's $w$, $s$ and $n$ as sums over the scales $j < N$ -/

section Sums

variable {n : ℕ} (e : Fin n → ℕ)

/-- The scales occurring, $J = \{e_i\}$, lie below $N = \max_i e_i + 1$. -/
theorem image_subset_range : univ.image e ⊆ range (univ.sup e + 1) := by
  intro j hj
  obtain ⟨i, -, rfl⟩ := mem_image.1 hj
  exact mem_range.2 (Nat.lt_succ_of_le (le_sup (mem_univ i)))

theorem jordanRank_eq_zero_of_not_mem {j : ℕ} (hj : j ∉ univ.image e) : jordanRank e j = 0 := by
  rw [jordanRank, card_eq_zero, filter_eq_empty_iff]
  intro i _ h
  exact hj (mem_image.2 ⟨i, mem_univ i, h⟩)

theorem jordanRank_ne_zero_of_mem {j : ℕ} (hj : j ∈ univ.image e) : jordanRank e j ≠ 0 := by
  obtain ⟨i, -, rfl⟩ := mem_image.1 hj
  rw [jordanRank, ← pos_iff_ne_zero, card_pos]
  exact ⟨i, mem_filter.2 ⟨mem_univ i, rfl⟩⟩

/-- $\sum_i e_i = \sum_{j<N} j\,n_j$. -/
theorem sum_e_eq : ∑ i, e i = ∑ j ∈ range (univ.sup e + 1), j * jordanRank e j := by
  rw [← sum_fiberwise_of_maps_to (g := e) (t := range (univ.sup e + 1))
    (fun i _ => mem_range.2 (Nat.lt_succ_of_le (le_sup (mem_univ i))))]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_congr rfl fun i hi => by rw [(mem_filter.1 hi).2], sum_const, smul_eq_mul, mul_comm]
  rfl

/-- $n = \sum_{j<N} n_j$. -/
theorem card_eq_sum : n = ∑ j ∈ range (univ.sup e + 1), jordanRank e j := by
  have := card_eq_sum_card_fiberwise (f := e) (s := univ) (t := range (univ.sup e + 1))
    (fun i _ => mem_range.2 (Nat.lt_succ_of_le (le_sup (mem_univ i))))
  rw [card_univ, Fintype.card_fin] at this
  exact this

/-- Twice Kitaoka's $w$ as a sum over the scales $j < N$. -/
theorem two_mul_w :
    2 * (∑ j ∈ univ.image e, (j * jordanRank e j * ∑ k ∈ (univ.image e).filter (fun k => j < k), jordanRank e k +
      j * (jordanRank e j * (jordanRank e j + 1) / 2))) =
    ∑ j ∈ range (univ.sup e + 1), (2 * j * jordanRank e j * ∑ k ∈ Ico (j + 1) (univ.sup e + 1), jordanRank e k +
      j * (jordanRank e j * (jordanRank e j + 1))) := by
  rw [mul_sum, ← sum_subset (image_subset_range e) (fun j _ hj => by
    simp [jordanRank_eq_zero_of_not_mem e hj])]
  refine sum_congr rfl fun j hj => ?_
  have hin : ∑ k ∈ (univ.image e).filter (fun k => j < k), jordanRank e k =
      ∑ k ∈ Ico (j + 1) (univ.sup e + 1), jordanRank e k := by
    refine sum_subset (fun k hk => ?_) (fun k hk hk' => ?_)
    · obtain ⟨hkJ, hjk⟩ := mem_filter.1 hk
      exact mem_Ico.2 ⟨hjk, mem_range.1 (image_subset_range e hkJ)⟩
    · apply jordanRank_eq_zero_of_not_mem
      intro hkJ
      exact hk' (mem_filter.2 ⟨hkJ, (mem_Ico.1 hk).1⟩)
  have h2 : 2 * (jordanRank e j * (jordanRank e j + 1) / 2) = jordanRank e j * (jordanRank e j + 1) :=
    Nat.mul_div_cancel' (Nat.even_mul_succ_self _).two_dvd
  rw [hin, mul_add, show 2 * (j * (jordanRank e j * (jordanRank e j + 1) / 2)) =
    j * (2 * (jordanRank e j * (jordanRank e j + 1) / 2)) by ring, h2]
  ring

end Sums

/-! ### The theorem -/

open QuadFormsKB.ConwaySloane QuadFormsKB.ConwaySloane.Mass in
/-- **Kitaoka 1993, Theorem 5.6.3 (I)** (p. 108), $p \ne 2$: the proposition `Theorem563odd`,
$\beta_p(N, N) = 2^sp^wPE$ for $N$ with Gram matrix $\operatorname{diag}(p^{e_i}u_i)$. Proved from the Conway–Sloane
$p$-mass formula (`ConwaySloane.Mass.pMassFormulaOdd`): the two local densities agree for $p$ odd, and the
Conway–Sloane product of diagonal factors and the cross term is Kitaoka's $2^sp^wPE$. -/
@[kb "kitaoka1993" "§5.6, Thm. 5.6.3 (I), p. 108 (proved, through the Conway–Sloane p-mass formula)"]
theorem theorem563odd_holds : Theorem563odd := by
  intro p _ hp2 n e u hu S J w
  classical
  -- integer representatives `a i ≡ u i (mod p)`
  let a : Fin n → ℤ := fun i => ((PadicInt.toZMod (u i)).val : ℤ)
  have hres : ∀ i, PadicInt.toZMod ((a i : ℤ) : ℤ_[p]) = PadicInt.toZMod (u i) := fun i => by
    simp only [a, Int.cast_natCast, map_natCast, ZMod.natCast_zmod_val]
  have ha : ∀ i, IsUnit ((a i : ℤ) : ℤ_[p]) := fun i => by
    by_contra h
    have hm : ((a i : ℤ) : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] := (IsLocalRing.mem_maximalIdeal _).2 h
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, hres] at hm
    have := (hu i).map PadicInt.toZMod
    rw [hm] at this
    exact not_isUnit_zero this
  choose c hc hcu using fun i => exists_unit_sq_mul hp2 (hu i) (ha i) (hres i).symm
  -- Step 1: `β_p(S, S) = β_p(A, A)` for the integer matrix `A = diag(p^{e_i} a_i)`
  let A : Matrix (Fin n) (Fin n) ℤ := diagonal fun i => (p : ℤ) ^ e i * a i
  have hA' : A.map (Int.castRingHom ℤ_[p]) = diagonal fun i => (p : ℤ_[p]) ^ e i * ((a i : ℤ) : ℤ_[p]) := by
    rw [diagonal_map (map_zero _)]
    congr 1; funext i; simp
  have hSA : S = (diagonal c)ᵀ * A.map (Int.castRingHom ℤ_[p]) * diagonal c := by
    rw [hA', diagonal_transpose, diagonal_mul_diagonal, diagonal_mul_diagonal]
    show diagonal (fun i => (p : ℤ_[p]) ^ e i * u i) = _
    congr 1; funext i; rw [← hcu i]; ring
  let c' : Fin n → ℤ_[p] := fun i => (((hc i).unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
  have hV : diagonal c * diagonal c' = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; simp [c']
  have hV' : diagonal c' * diagonal c = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; simp [c']
  have hAt : (A.map (Int.castRingHom ℤ_[p]))ᵀ = A.map (Int.castRingHom ℤ_[p]) := by
    rw [hA', diagonal_transpose]
  have step1 : betaP p S S = betaP p (A.map (Int.castRingHom ℤ_[p])) (A.map (Int.castRingHom ℤ_[p])) := by
    rw [hSA]; exact betaP_conj hAt hAt hV hV' hV hV'
  -- Step 2: Kitaoka's density is the Conway–Sloane density
  rw [step1, betaP_map_eq_alphaP hp2]
  -- Step 3: the Conway–Sloane `p`-mass of `A`
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have ha0 : ∀ i, a i ≠ 0 := fun i h0 => by
    have := ha i; rw [h0, Int.cast_zero] at this; exact not_isUnit_zero this
  have hAsymm : A.IsSymm := by
    rw [Matrix.IsSymm, diagonal_transpose]
  have hdet : A.det ≠ 0 := by
    rw [det_diagonal]
    exact prod_ne_zero_iff.2 fun i _ => mul_ne_zero (pow_ne_zero _ hp0) (ha0 i)
  set σ : OddSymbol := oddSymbolOfDiag p e (fun i => (((a i : ℤ) : ℤ_[p]) : ℚ_[p])) with hσdef
  set N : ℕ := univ.sup e + 1 with hNdef
  have hσ : IsOddSymbolOf p (A.map (Int.cast : ℤ → ℚ_[p])) σ := by
    refine ⟨e, fun i => (((a i : ℤ) : ℤ_[p]) : ℚ_[p]), fun i => ?_, ?_, rfl⟩
    · rw [PadicInt.norm_coe]; exact PadicInt.isUnit_iff.1 (ha i)
    · convert Cassels.ZpEquiv.refl _ using 1
      ext i j
      by_cases hij : i = j
      · subst hij; simp [A]
      · simp [A, hij]
  have hN : ∀ k, N ≤ k → σ k = OddFactor.trivial := by
    intro k hk
    have hempty : IsEmpty {i // e i = k} := ⟨fun x => by
      have := le_sup (f := e) (mem_univ x.1); rw [x.2] at this; omega⟩
    have h0 : Fintype.card {i // e i = k} = 0 := Fintype.card_eq_zero
    simp only [hσdef, oddSymbolOfDiag, OddFactor.trivial, h0, Finset.univ_eq_empty, prod_empty]
    rw [if_pos ⟨1, (one_mul 1).symm⟩]
  have hpm := (pMassFormulaOdd hp2).pMass_eq A hAsymm hdet σ N hσ hN
  have hα := alphaP_pos (Fact.out : p.Prime) hAsymm hdet
  -- `v_p(det A) = Σ e_i`
  have hval : padicValInt p A.det = ∑ i, e i := by
    rw [det_diagonal, prod_mul_distrib, prod_pow_eq_pow_sum]
    have hndvd : ¬ (p : ℤ) ∣ ∏ i, a i := by
      intro hdvd
      obtain ⟨i, -, hi⟩ := (Prime.dvd_finset_prod_iff (Int.prime_iff_natAbs_prime.2 (by simpa using
        (Fact.out : p.Prime))) _).1 hdvd
      obtain ⟨m, hm⟩ := hi
      have hu' := ha i
      rw [hm, Int.cast_mul, Int.cast_natCast] at hu'
      have : ¬ IsUnit ((p : ℤ_[p])) := by
        rw [PadicInt.isUnit_iff, PadicInt.norm_p]
        have := (Fact.out : p.Prime).one_lt
        have h1 : (1 : ℝ) < p := by exact_mod_cast this
        intro h; rw [inv_eq_one] at h; linarith
      exact this (isUnit_of_mul_isUnit_left hu')
    rw [padicValInt.mul (pow_ne_zero _ hp0) (prod_ne_zero_iff.2 fun i _ => ha0 i),
      show ((p : ℤ) ^ (∑ i, e i)) = (((p ^ ∑ i, e i : ℕ)) : ℤ) by push_cast; rfl,
      padicValInt.of_nat, padicValNat.prime_pow, padicValInt.eq_zero_of_not_dvd hndvd, add_zero]
  -- Step 3': `α_p(A) = p^{s(n+1)/2} / m_p(A)` and `m_p(A)` is the Conway–Sloane product
  have hα' : ConwaySloane.Mass.alphaP p A =
      (p : ℝ) ^ (((∑ i, e i : ℕ) : ℝ) * ((n : ℝ) + 1) / 2) / pMassOdd p σ N := by
    rw [← hpm, pMassDensity, hval]
    have hP : (0 : ℝ) < (p : ℝ) ^ (((∑ i, e i : ℕ) : ℝ) * ((n : ℝ) + 1) / 2) := by
      have : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
      positivity
    field_simp
  rw [hα']
  -- Step 4: the arithmetic identity
  have hdim : ∀ k, (σ k).dim = jordanRank e k := fun k => card_subtype_eq_jordanRank e k
  have hcross : crossExp (fun k => (σ k).dim) N = crossExp (jordanRank e) N := by
    congr 1; funext k; exact hdim k
  have hw : 2 * w + crossExp (jordanRank e) N = (∑ i, e i) * (n + 1) := by
    have hexp := exponent_identity (jordanRank e) N
    rw [← two_mul_w e, ← sum_e_eq e, ← card_eq_sum e] at hexp
    exact hexp
  have hpR : (0 : ℝ) ≤ p := by positivity
  have hsq : (p : ℝ) ^ (((∑ i, e i : ℕ) : ℝ) * ((n : ℝ) + 1) / 2) =
      (p : ℝ) ^ w * Real.sqrt p ^ crossExp (jordanRank e) N := by
    have h1 : (p : ℝ) ^ (((∑ i, e i : ℕ) : ℝ) * ((n : ℝ) + 1) / 2) =
        Real.sqrt p ^ ((∑ i, e i) * (n + 1)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hpR]
      congr 1; push_cast; ring
    rw [h1, ← hw, pow_add, pow_mul, Real.sq_sqrt hpR]
  unfold pMassOdd
  rw [hcross, hsq]
  have hsqrt : Real.sqrt p ^ crossExp (jordanRank e) N ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.2 (by exact_mod_cast (Fact.out : p.Prime).pos)
    positivity
  -- the diagonal product
  have hdiag : ((∏ k ∈ range N, (oddSpecies p (σ k)).diagFactor p : ℚ) : ℝ)⁻¹ =
      2 ^ J.card * (∏ j ∈ J, kitP p (jordanRank e j / 2)) *
        ∏ j ∈ J, (1 + chiJ p e u j * (p : ℝ) ^ (-((jordanRank e j : ℝ) / 2)))⁻¹ := by
    push_cast
    rw [← prod_inv_distrib]
    rw [← prod_subset (image_subset_range e) (fun k _ hk => by
      rw [Species.diagFactor, if_pos (by show (σ k).dim = 0; rw [hdim]; exact jordanRank_eq_zero_of_not_mem e hk)]
      simp)]
    rw [prod_congr rfl fun j hj => inv_diagFactor_eq hp2 (σ j)
      (by rw [hdim]; exact jordanRank_ne_zero_of_mem e hj) (chiJ p e u j)
      (fun h => by rw [hdim] at h; simp [chiJ, h])
      (fun h => by
        rw [hdim] at h
        exact (sign_eq_chiJ hp2 e u hu a hres ha j h (jordanRank_ne_zero_of_mem e hj)).symm)]
    simp only [hdim]
    rw [prod_mul_distrib, prod_mul_distrib, prod_const]
  rw [div_eq_mul_inv, mul_inv, hdiag]
  field_simp

end QuadFormsKB.Kitaoka.Density
