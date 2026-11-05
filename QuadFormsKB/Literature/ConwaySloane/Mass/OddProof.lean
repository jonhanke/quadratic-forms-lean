/-
# Conway–Sloane 1988, formula (3) at odd primes: proof

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), (3), p. 263; Table 1 (lower half) and Table 2, p. 264; (18), p. 281 (bibliography key `conwaysloane1988`).

This file proves the named input `PMassFormulaOdd p` for every odd prime $p$: the $p$-mass
$m_p(f) = p^{s(n+1)/2}/\alpha_p(f)$ defined by counting (§12, `pMassDensity`) equals the right-hand side of (3) computed
from the $p$-adic symbol (`pMassOdd`).

**Route** (purely local).
1. $N(p^r)$ is an invariant of $\mathbb Z_p$-equivalence (`countN_eq_of_zpEquiv`), and so is the exponent $s$
   (`padicValInt_det_eq_of_zpEquiv`).
2. **Splitting off the unimodular constituent** (`pMassDensity_blocks`): for $A = U \perp pB$ with $p \nmid \det U$,
   the block count identity (`card_fromBlocks_odd`) gives $N_r(A) = p^{rab}N_r(U)N_r(pB)$ at every level $r$, hence
   $\alpha_p(A) = \alpha_p(U)\alpha_p(pB)$ and $m_p(A) = m_p(U)\,m_p(B)\,p^{as/2}$, $s = \operatorname{ord}_p\det A$.
3. **The diagonal model** of a symbol $\sigma$ (`model`): $\bigoplus_k p^k\operatorname{diag}(c_k, 1, \dots, 1)$ with
   $c_k = 1$ for the sign $+$ and a fixed quadratic non-residue $c$ for the sign $-$. Its symbol is $\sigma$
   (`isOddSymbolOf_model`), so by Theorem 9 every form with symbol $\sigma$ is $\mathbb Z_p$-equivalent to it.
4. Induction over the constituents (`pMassDensity_model`): the unimodular constituent contributes
   $m_p = \mathrm{std}_p = M_p(\text{species})$ (`pMassDensity_eq_stdP`, `pMassOdd_unimodular`), and $p^{as/2}$ is the
   part of the cross-product $\prod_{q<q'}(q'/q)^{\frac12 n(q)n(q')}$ that involves the first constituent.

Indices are 0-based: the constituent of scale $p^k$ is `σ k`.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.Formula
import QuadFormsKB.Literature.ConwaySloane.Mass.BlockCount
import QuadFormsKB.Literature.ConwaySloane.Mass.StdForm

set_option linter.unusedSectionVars false

namespace QuadFormsKB.ConwaySloane.Mass

open Matrix Filter

/-! ### Counting solutions: reindexing and congruence -/

section Count

variable {R : Type*} [CommRing R] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The number of solutions of $X^{\mathsf T}MX = M$ does not change when the index set is renamed. -/
theorem card_sol_submatrix (e : κ ≃ ι) (M : Matrix ι ι R) :
    Nat.card {X : Matrix κ κ R // Xᵀ * M.submatrix e e * X = M.submatrix e e} =
      Nat.card {X : Matrix ι ι R // Xᵀ * M * X = M} := by
  let f := (reindexAlgEquiv R R e)
  refine Nat.card_congr (Equiv.subtypeEquiv f.toEquiv fun X => ?_)
  have hM : M.submatrix e e = f.symm M := by
    simp [f, symm_reindexAlgEquiv, coe_reindexAlgEquiv, reindex_apply]
  have hT : (f X)ᵀ = f Xᵀ := by simp [f, coe_reindexAlgEquiv, reindex_apply, transpose_submatrix]
  rw [hM]
  constructor
  · intro h
    have := congrArg f h
    simpa [map_mul, hT] using this
  · intro h
    apply f.injective
    simp only [AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe] at h
    rw [map_mul, map_mul, AlgEquiv.apply_symm_apply, ← hT, h]

/-- The number of solutions of $X^{\mathsf T}MX = M$ is invariant under $M \mapsto G^{\mathsf T}MG$, $G$ invertible. -/
theorem card_sol_congr {G : Matrix ι ι R} (hG : IsUnit G) (S : Matrix ι ι R) :
    Nat.card {Y : Matrix ι ι R // Yᵀ * (Gᵀ * S * G) * Y = Gᵀ * S * G} =
      Nat.card {Y : Matrix ι ι R // Yᵀ * S * Y = S} := by
  obtain ⟨u, rfl⟩ := hG
  set g : Matrix ι ι R := (u : Matrix ι ι R)
  set gi : Matrix ι ι R := ↑u⁻¹
  have h1 : g * gi = 1 := Units.mul_inv u
  have h2 : gi * g = 1 := Units.inv_mul u
  have h1t : giᵀ * gᵀ = 1 := by rw [← transpose_mul, h1, transpose_one]
  have h2t : gᵀ * giᵀ = 1 := by rw [← transpose_mul, h2, transpose_one]
  refine Nat.card_congr
    { toFun := fun Y => ⟨g * Y.1 * gi, ?_⟩
      invFun := fun Y => ⟨gi * Y.1 * g, ?_⟩
      left_inv := fun Y => Subtype.ext ?_
      right_inv := fun Y => Subtype.ext ?_ }
  · have h := Y.2
    calc (g * Y.1 * gi)ᵀ * S * (g * Y.1 * gi) = giᵀ * (Y.1ᵀ * (gᵀ * S * g) * Y.1) * gi := by
          simp only [transpose_mul, Matrix.mul_assoc]
      _ = S := by rw [h]; simp only [← Matrix.mul_assoc, h1t, Matrix.one_mul]; rw [Matrix.mul_assoc, h1,
          Matrix.mul_one]
  · have h := Y.2
    calc (gi * Y.1 * g)ᵀ * (gᵀ * S * g) * (gi * Y.1 * g) =
          gᵀ * (Y.1ᵀ * ((giᵀ * gᵀ) * S * (g * gi)) * Y.1) * g := by
          simp only [transpose_mul, Matrix.mul_assoc]
      _ = gᵀ * S * g := by rw [h1t, h1, Matrix.one_mul, Matrix.mul_one, h]
  · show gi * (g * Y.1 * gi) * g = Y.1
    simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]; rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  · show g * (gi * Y.1 * g) * gi = Y.1
    simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]; rw [Matrix.mul_assoc, h1, Matrix.mul_one]

end Count

/-! ### $\mathbb Z_p$-equivalence invariance -/

section ZpInv

variable {n : ℕ} {p : ℕ} [hp : Fact p.Prime]

open QuadFormsKB.Cassels

/-- A $\mathbb Z_p$-equivalence of integral forms reduces modulo every $p^r$ to a congruence by an invertible matrix. -/
theorem exists_unit_congr_of_zpEquiv {A B : Matrix (Fin n) (Fin n) ℤ}
    (h : ZpEquiv (A.map (Int.cast : ℤ → ℚ_[p])) (B.map (Int.cast : ℤ → ℚ_[p]))) (r : ℕ) :
    ∃ G : Matrix (Fin n) (Fin n) (ZMod (p ^ r)), IsUnit G ∧
      Gᵀ * A.map (Int.castRingHom (ZMod (p ^ r))) * G = B.map (Int.castRingHom (ZMod (p ^ r))) := by
  obtain ⟨T, hT⟩ := h
  let φ : ℤ_[p] →+* ZMod (p ^ r) := PadicInt.toZModPow r
  -- the equivalence over `ℤ_p`
  have hZ : T.valᵀ * A.map (Int.castRingHom ℤ_[p]) * T.val = B.map (Int.castRingHom ℤ_[p]) := by
    have hinj : Function.Injective (fun M : Matrix (Fin n) (Fin n) ℤ_[p] => M.map PadicInt.Coe.ringHom) :=
      Matrix.map_injective (fun x y hxy => Subtype.ext hxy)
    apply hinj
    beta_reduce
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
    have e0 : ∀ C : Matrix (Fin n) (Fin n) ℤ,
        (C.map (Int.castRingHom ℤ_[p])).map PadicInt.Coe.ringHom = C.map (Int.cast : ℤ → ℚ_[p]) := fun C => by
      ext i j; simp
    rw [e0, e0]; exact hT
  refine ⟨T.val.map φ, ?_, ?_⟩
  · exact (Units.map (RingHom.mapMatrix φ).toMonoidHom T).isUnit
  · have := congrArg (fun M => M.map φ) hZ
    simp only [Matrix.map_mul, Matrix.transpose_map] at this
    have e1 : ∀ C : Matrix (Fin n) (Fin n) ℤ,
        (C.map (Int.castRingHom ℤ_[p])).map φ = C.map (Int.castRingHom (ZMod (p ^ r))) := fun C => by
      ext i j; simp
    rw [e1, e1] at this
    exact this

/-- **$N(p^r)$ is an invariant of $\mathbb Z_p$-equivalence** (Conway–Sloane 1988, (18), p. 281). -/
@[kb "conwaysloane1988" "(18), p. 281 (invariance under Z_p-equivalence)"]
theorem countN_eq_of_zpEquiv {A B : Matrix (Fin n) (Fin n) ℤ}
    (h : ZpEquiv (A.map (Int.cast : ℤ → ℚ_[p])) (B.map (Int.cast : ℤ → ℚ_[p]))) (r : ℕ) :
    countN p r B = countN p r A := by
  obtain ⟨G, hG, hGe⟩ := exists_unit_congr_of_zpEquiv h r
  unfold countN
  rw [← hGe, card_sol_congr hG]

/-- **$\alpha_p$ is an invariant of $\mathbb Z_p$-equivalence.** -/
theorem alphaP_eq_of_zpEquiv {A B : Matrix (Fin n) (Fin n) ℤ}
    (h : ZpEquiv (A.map (Int.cast : ℤ → ℚ_[p])) (B.map (Int.cast : ℤ → ℚ_[p]))) :
    alphaP p B = alphaP p A := by
  unfold alphaP
  simp only [countN_eq_of_zpEquiv h]

/-- The exponent $s$ ($p^s \,\|\, \det$) is an invariant of $\mathbb Z_p$-equivalence. -/
theorem padicValInt_det_eq_of_zpEquiv {A B : Matrix (Fin n) (Fin n) ℤ}
    (h : ZpEquiv (A.map (Int.cast : ℤ → ℚ_[p])) (B.map (Int.cast : ℤ → ℚ_[p]))) (hA : A.det ≠ 0)
    (hB : B.det ≠ 0) : padicValInt p B.det = padicValInt p A.det := by
  have key : ∀ r : ℕ, ((p : ℤ) ^ r ∣ A.det ↔ (p : ℤ) ^ r ∣ B.det) := by
    intro r
    obtain ⟨G, hG, hGe⟩ := exists_unit_congr_of_zpEquiv h r
    have hd := congrArg Matrix.det hGe
    have md : ∀ C : Matrix (Fin n) (Fin n) ℤ,
        (C.map (Int.castRingHom (ZMod (p ^ r)))).det = Int.castRingHom (ZMod (p ^ r)) C.det := fun C => by
      rw [RingHom.map_det]; rfl
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, md, md] at hd
    have hu : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hG
    have e : ∀ z : ℤ, (p : ℤ) ^ r ∣ z ↔ (Int.castRingHom (ZMod (p ^ r)) z = 0) := fun z => by
      rw [eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rfl
    rw [e, e, ← hd]
    constructor
    · intro h0; rw [h0]; simp
    · intro h0
      exact hu.mul_right_eq_zero.mp (hu.mul_left_eq_zero.mp h0)
  have hle : ∀ {a b : ℤ}, a ≠ 0 → b ≠ 0 → (∀ r : ℕ, ((p : ℤ) ^ r ∣ a ↔ (p : ℤ) ^ r ∣ b)) →
      padicValInt p a ≤ padicValInt p b := fun {a b} ha hb hab => by
    have h1 : (p : ℤ) ^ padicValInt p a ∣ a := padicValInt_dvd a
    have h2 := (padicValInt_dvd_iff (padicValInt p a) b).mp ((hab _).mp h1)
    rcases h2 with h2 | h2
    · exact absurd h2 hb
    · exact h2
  exact le_antisymm (hle hB hA fun r => (key r).symm) (hle hA hB key)

/-- **The $p$-mass is an invariant of $\mathbb Z_p$-equivalence.** -/
theorem pMassDensity_eq_of_zpEquiv {A B : Matrix (Fin n) (Fin n) ℤ}
    (h : ZpEquiv (A.map (Int.cast : ℤ → ℚ_[p])) (B.map (Int.cast : ℤ → ℚ_[p]))) (hA : A.det ≠ 0)
    (hB : B.det ≠ 0) : pMassDensity p B = pMassDensity p A := by
  unfold pMassDensity
  rw [alphaP_eq_of_zpEquiv h, padicValInt_det_eq_of_zpEquiv h hA hB]

end ZpInv

/-! ### Splitting off the unimodular constituent -/

section Blocks

variable {p : ℕ} [hp : Fact p.Prime]

/-- An integer prime to $p$ is a unit modulo $p^r$. -/
theorem isUnit_intCast_of_not_dvd {z : ℤ} (hz : ¬ (p : ℤ) ∣ z) (r : ℕ) : IsUnit (z : ZMod (p ^ r)) := by
  have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hc : IsCoprime ((p : ℤ) ^ r) z := ((Prime.coprime_iff_not_dvd hpr).mpr hz).pow_left
  obtain ⟨u, v, huv⟩ := hc
  have := congrArg (Int.cast : ℤ → ZMod (p ^ r)) huv
  push_cast at this
  rw [show ((p : ZMod (p ^ r)) ^ r) = 0 by exact_mod_cast ZMod.natCast_self (p ^ r), mul_zero, zero_add] at this
  exact isUnit_iff_exists_inv.mpr ⟨v, by rw [mul_comm]; exact this⟩

/-- The block matrix $U \perp pB$ on $\mathrm{Fin}(a + b)$. -/
def blk (p : ℕ) {a b : ℕ} (U : Matrix (Fin a) (Fin a) ℤ) (B : Matrix (Fin b) (Fin b) ℤ) :
    Matrix (Fin (a + b)) (Fin (a + b)) ℤ :=
  (fromBlocks U 0 0 ((p : ℤ) • B)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

/-- **The block count identity over $\mathbb Z/p^r$, $p$ odd**: $N_r(U \perp pB) = p^{rab}N_r(U)N_r(pB)$ when
$p \nmid \det U$. -/
@[kb "conwaysloane1988" "(18), p. 281 (splitting off a unimodular constituent, p odd)"]
theorem countN_blk (hp2 : p ≠ 2) {a b : ℕ} {U : Matrix (Fin a) (Fin a) ℤ} {B : Matrix (Fin b) (Fin b) ℤ}
    (hUs : U.IsSymm) (hU : ¬ (p : ℤ) ∣ U.det) (hBs : B.IsSymm) (r : ℕ) :
    countN p r (blk p U B) = (p ^ r) ^ (b * a) * countN p r U * countN p r ((p : ℤ) • B) := by
  set φ := Int.castRingHom (ZMod (p ^ r))
  have hsm : ((p : ℤ) • B).map φ = (p : ZMod (p ^ r)) • B.map φ := by
    ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, smul_eq_mul,
      map_mul, map_natCast]
  have hmap : (blk p U B).map φ =
      (fromBlocks (U.map φ) 0 0 ((p : ZMod (p ^ r)) • B.map φ)).submatrix finSumFinEquiv.symm
        finSumFinEquiv.symm := by
    rw [blk, ← Matrix.submatrix_map, fromBlocks_map, Matrix.map_zero _ (map_zero φ), Matrix.map_zero _ (map_zero φ),
      hsm]
  have h2 : IsUnit (2 : ZMod (p ^ r)) := by
    have := isUnit_intCast_of_not_dvd (p := p) (z := 2) (by
      intro h
      have : (p : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) h
      have := hp.out.two_le
      have : p = 2 := by omega
      exact hp2 this) r
    simpa using this
  have hUu : IsUnit (U.map φ).det := by
    rw [show (U.map φ).det = φ U.det by rw [RingHom.map_det]; rfl]
    simpa [φ] using isUnit_intCast_of_not_dvd hU r
  have hπ : IsNilpotent (p : ZMod (p ^ r)) := ⟨r, by exact_mod_cast ZMod.natCast_self (p ^ r)⟩
  have hUs' : (U.map φ)ᵀ = U.map φ := by rw [← Matrix.transpose_map, hUs.eq]
  have hBs' : (B.map φ)ᵀ = B.map φ := by rw [← Matrix.transpose_map, hBs.eq]
  unfold countN
  rw [hmap, card_sol_submatrix, card_fromBlocks_odd h2 hUs' hUu hπ hBs', hsm]
  congr 2
  rw [Fintype.card_eq_nat_card, Matrix.card_matrix]
  simp [Nat.card_eq_fintype_card, ZMod.card, mul_comm]

theorem tri_add (a b : ℕ) : (a + b) * (a + b - 1) / 2 = a * (a - 1) / 2 + b * (b - 1) / 2 + b * a := by
  rw [← Nat.choose_two_right, ← Nat.choose_two_right, ← Nat.choose_two_right, Nat.add_choose_eq]
  simp [Finset.Nat.antidiagonal_succ]
  ring

theorem blk_isSymm {a b : ℕ} {U : Matrix (Fin a) (Fin a) ℤ} {B : Matrix (Fin b) (Fin b) ℤ} (hUs : U.IsSymm)
    (hBs : B.IsSymm) : (blk p U B).IsSymm := by
  unfold blk Matrix.IsSymm
  rw [Matrix.transpose_submatrix, fromBlocks_transpose, hUs.eq, transpose_smul, hBs.eq]
  simp only [transpose_zero]

theorem blk_det {a b : ℕ} (U : Matrix (Fin a) (Fin a) ℤ) (B : Matrix (Fin b) (Fin b) ℤ) :
    (blk p U B).det = U.det * ((p : ℤ) ^ b * B.det) := by
  unfold blk
  rw [Matrix.det_submatrix_equiv_self, det_fromBlocks_zero₂₁, Matrix.det_smul, Fintype.card_fin]

theorem smul_isSymm {b : ℕ} {B : Matrix (Fin b) (Fin b) ℤ} (hBs : B.IsSymm) : ((p : ℤ) • B).IsSymm := by
  unfold Matrix.IsSymm; rw [transpose_smul, hBs.eq]

theorem smul_det_ne {b : ℕ} {B : Matrix (Fin b) (Fin b) ℤ} (hB : B.det ≠ 0) : ((p : ℤ) • B).det ≠ 0 := by
  rw [Matrix.det_smul, Fintype.card_fin]
  exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)) hB

/-- **$\alpha_p(U \perp pB) = \alpha_p(U)\,\alpha_p(pB)$** for $p$ odd and $p \nmid \det U$. -/
@[kb "conwaysloane1988" "§12, p. 281 (splitting off a unimodular constituent, p odd)"]
theorem alphaP_blk (hp2 : p ≠ 2) {a b : ℕ} {U : Matrix (Fin a) (Fin a) ℤ} {B : Matrix (Fin b) (Fin b) ℤ}
    (hUs : U.IsSymm) (hU : ¬ (p : ℤ) ∣ U.det) (hBs : B.IsSymm) (hB : B.det ≠ 0) :
    alphaP p (blk p U B) = alphaP p U * alphaP p ((p : ℤ) • B) := by
  have hU0 : U.det ≠ 0 := fun h => hU (h ▸ dvd_zero _)
  have hblk0 : (blk p U B).det ≠ 0 := by
    rw [blk_det]; exact mul_ne_zero hU0 (mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)) hB)
  obtain ⟨r1, h1⟩ := alphaP_stabilizes hp.out (blk_isSymm (p := p) hUs hBs) hblk0
  obtain ⟨r2, h2⟩ := alphaP_stabilizes hp.out hUs hU0
  obtain ⟨r3, h3⟩ := alphaP_stabilizes hp.out (smul_isSymm (p := p) hBs) (smul_det_ne (p := p) hB)
  set r := max r1 (max r2 r3)
  rw [← h1 r (le_max_left _ _), ← h2 r (le_trans (le_max_left _ _) (le_max_right _ _)),
    ← h3 r (le_trans (le_max_right _ _) (le_max_right _ _)), countN_blk hp2 hUs hU hBs, tri_add]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  push_cast
  rw [mul_add, mul_add, pow_add, pow_add, ← pow_mul, mul_comm (r : ℕ) (b * a)]
  field_simp

/-- **The $p$-mass of $U \perp pB$** ($p$ odd, $p \nmid \det U$): $m_p(U \perp pB) = m_p(U)\,m_p(B)\,p^{as/2}$ with
$s = \operatorname{ord}_p\det(U \perp pB) = b + \operatorname{ord}_p\det B$; the factor $p^{as/2}$ is the part of the
cross-product of (3) between the unimodular constituent and the others. -/
@[kb "conwaysloane1988" "(3), p. 263 (one step of the induction over the constituents, p odd)"]
theorem pMassDensity_blk (hp2 : p ≠ 2) {a b : ℕ} {U : Matrix (Fin a) (Fin a) ℤ} {B : Matrix (Fin b) (Fin b) ℤ}
    (hUs : U.IsSymm) (hU : ¬ (p : ℤ) ∣ U.det) (hBs : B.IsSymm) (hB : B.det ≠ 0) :
    pMassDensity p (blk p U B) = pMassDensity p U * pMassDensity p B *
      (p : ℝ) ^ ((((b + padicValInt p B.det : ℕ) : ℝ) * a) / 2) := by
  have hU0 : U.det ≠ 0 := fun h => hU (h ▸ dvd_zero _)
  have hvU : padicValInt p U.det = 0 := padicValInt.eq_zero_of_not_dvd hU
  have hv : padicValInt p (blk p U B).det = b + padicValInt p B.det := by
    rw [blk_det, padicValInt.mul hU0 (mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)) hB), hvU,
      zero_add, padicValInt.mul (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)) hB]
    congr 1
    unfold padicValInt
    simp
  have hαB := alphaP_smul_prime hp.out hBs hB
  have hαU := (alphaP_pos hp.out hUs hU0).ne'
  have hαB0 := (alphaP_pos hp.out hBs hB).ne'
  unfold pMassDensity
  rw [alphaP_blk hp2 hUs hU hBs hB, hαB, hv, hvU, ← Real.rpow_natCast (p : ℝ) (b * (b + 1) / 2), cast_half]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  simp only [Nat.cast_zero, zero_mul, zero_div, Real.rpow_zero]
  set s : ℝ := ((b + padicValInt p B.det : ℕ) : ℝ)
  have hs : s = (b : ℝ) + (padicValInt p B.det : ℝ) := by simp [s]
  have e : (p : ℝ) ^ (s * (((a + b : ℕ) : ℝ) + 1) / 2) = (p : ℝ) ^ ((b : ℝ) * ((b : ℝ) + 1) / 2) *
      (p : ℝ) ^ ((padicValInt p B.det : ℝ) * ((b : ℝ) + 1) / 2) * (p : ℝ) ^ (s * a / 2) := by
    rw [← Real.rpow_add hp0, ← Real.rpow_add hp0]
    congr 1
    rw [hs]; push_cast; ring
  rw [e]
  have : (0 : ℝ) < (p : ℝ) ^ ((b : ℝ) * ((b : ℝ) + 1) / 2) := by positivity
  field_simp

end Blocks

/-! ### The recursion of the right-hand side of (3) -/

section Recursion

/-- The symbol shifted down by one scale: `shiftSym σ k = σ (k + 1)`. -/
def shiftSym (σ : OddSymbol) : OddSymbol := fun k => σ (k + 1)

theorem crossExp_succ (dim : ℕ → ℕ) (N : ℕ) :
    crossExp dim (N + 1) = crossExp (fun k => dim (k + 1)) N +
      dim 0 * ∑ k ∈ Finset.range N, (k + 1) * dim (k + 1) := by
  unfold crossExp
  rw [Finset.sum_range_succ']
  simp only [Finset.range_zero, Finset.sum_empty, add_zero]
  have : ∀ k' : ℕ, ∑ k ∈ Finset.range (k' + 1), (k' + 1 - k) * dim k * dim (k' + 1) =
      ∑ k ∈ Finset.range k', (k' - k) * dim (k + 1) * dim (k' + 1) + (k' + 1) * dim 0 * dim (k' + 1) := by
    intro k'
    rw [Finset.sum_range_succ']
    congr 1
    · exact Finset.sum_congr rfl fun k _ => by rw [Nat.add_sub_add_right]
  simp only [this, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => by ring

theorem sqrt_pow_eq_rpow (p m : ℕ) : Real.sqrt p ^ m = (p : ℝ) ^ ((m : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p)]
  ring_nf

/-- **The recursion of (3) over the constituents** ($p$ odd): splitting off the constituent of scale $1$,
$m_p(\sigma) = M_p(f_1)\cdot m_p(\sigma')\cdot \sqrt p^{\,n_1\sum_{k}(k+1)n_{p^{k+1}}}$, $\sigma'$ the shifted symbol. -/
theorem pMassOdd_succ (p : ℕ) (σ : OddSymbol) (N : ℕ) :
    pMassOdd p σ (N + 1) = ((oddSpecies p (σ 0)).diagFactor p : ℝ) * pMassOdd p (shiftSym σ) N *
      Real.sqrt p ^ ((σ 0).dim * ∑ k ∈ Finset.range N, (k + 1) * (σ (k + 1)).dim) := by
  unfold pMassOdd
  rw [crossExp_succ, pow_add, Finset.prod_range_succ']
  simp only [shiftSym]
  push_cast
  ring

end Recursion

/-! ### The diagonal model of a symbol -/

section Model

/-- The total dimension $\sum_{k<N} n_{p^k}$ of the constituents below $p^N$. -/
def totDim (σ : OddSymbol) : ℕ → ℕ
  | 0 => 0
  | N + 1 => (σ 0).dim + totDim (shiftSym σ) N

/-- The diagonal entries of the unit form $\operatorname{diag}(c_k, 1, \dots, 1)$ of a constituent: $c$ in position
$0$ if the sign is $-$, and $1$ otherwise. -/
def unitEntries (c : ℤ) (f : OddFactor) : Fin f.dim → ℤ := fun i => if i.val = 0 ∧ f.sign = .minus then c else 1

/-- **The diagonal model** of a $p$-adic symbol: $\bigoplus_{k<N} p^k\operatorname{diag}(c_k, 1, \dots, 1)$, with
$c_k = 1$ if $\varepsilon_{p^k} = +$ and $c_k = c$ (a quadratic non-residue) if $\varepsilon_{p^k} = -$; built
recursively as $\operatorname{diag}(c_0, 1, \dots, 1) \perp p\,(\text{model of the shifted symbol})$. -/
def model (p : ℕ) (c : ℤ) (σ : OddSymbol) : (N : ℕ) → Matrix (Fin (totDim σ N)) (Fin (totDim σ N)) ℤ
  | 0 => 0
  | N + 1 => blk p (diagonal (unitEntries c (σ 0))) (model p c (shiftSym σ) N)

/-- The diagonal entries of the model. -/
def modelD (p : ℕ) (c : ℤ) (σ : OddSymbol) : (N : ℕ) → Fin (totDim σ N) → ℤ
  | 0 => Fin.elim0
  | N + 1 => Fin.append (unitEntries c (σ 0)) (fun j => (p : ℤ) * modelD p c (shiftSym σ) N j)

variable {p : ℕ} [hp : Fact p.Prime]

theorem blk_diagonal {a b : ℕ} (d₁ : Fin a → ℤ) (d₂ : Fin b → ℤ) :
    blk p (diagonal d₁) (diagonal d₂) = diagonal (Fin.append d₁ fun j => (p : ℤ) * d₂ j) := by
  ext i j
  unfold blk
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
    simp only [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, submatrix_apply,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, diagonal_apply,
      Fin.append_left, Fin.append_right, Matrix.zero_apply, Fin.castAdd_inj, Fin.natAdd_inj]
  all_goals first
    | (rw [eq_comm, ite_eq_right_iff]; intro h; have := congrArg Fin.val h; simp at this; omega)
    | (rw [Matrix.smul_apply, diagonal_apply, smul_eq_mul]; split_ifs <;> simp)

theorem model_eq_diagonal (c : ℤ) (σ : OddSymbol) (N : ℕ) : model p c σ N = diagonal (modelD p c σ N) := by
  induction N generalizing σ with
  | zero => ext i; exact i.elim0
  | succ N ih =>
    show blk p (diagonal (unitEntries c (σ 0))) (model p c (shiftSym σ) N) =
      diagonal (Fin.append (unitEntries c (σ 0)) (fun j => (p : ℤ) * modelD p c (shiftSym σ) N j))
    rw [ih, blk_diagonal]

theorem model_isSymm (c : ℤ) (σ : OddSymbol) (N : ℕ) : (model p c σ N).IsSymm := by
  rw [model_eq_diagonal]; exact diagonal_transpose _

theorem unitEntries_prod (c : ℤ) (f : OddFactor) (hf : f.dim ≠ 0) :
    ∏ i, unitEntries c f i = if f.sign = .minus then c else 1 := by
  obtain ⟨m, hm⟩ : ∃ m, f.dim = m + 1 := ⟨f.dim - 1, by omega⟩
  have : ∀ g : Fin f.dim → ℤ, ∏ i, g i = g ⟨0, by omega⟩ * ∏ i : {i : Fin f.dim // i.val ≠ 0}, g i := by
    intro g
    rw [← Finset.prod_subtype (Finset.univ.filter fun i : Fin f.dim => i.val ≠ 0) (by simp),
      ← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ ⟨0, by omega⟩)]
    congr 1
    apply Finset.prod_congr _ (fun _ _ => rfl)
    ext i; simp [Fin.ext_iff]
  rw [this]
  rw [Finset.prod_eq_one fun i _ => by simp [unitEntries, i.2]]
  simp [unitEntries]

theorem unitEntries_det (c : ℤ) (f : OddFactor) (hf : f.dim ≠ 0) :
    (diagonal (unitEntries c f)).det = if f.sign = .minus then c else 1 := by
  rw [det_diagonal, unitEntries_prod c f hf]

theorem not_dvd_unitEntries_det {c : ℤ} (hc : ¬ (p : ℤ) ∣ c) (f : OddFactor) :
    ¬ (p : ℤ) ∣ (diagonal (unitEntries c f)).det := by
  rw [det_diagonal]
  intro h
  obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff_prime_int.mp hp.out) _).mp h
  unfold unitEntries at hi
  split_ifs at hi
  · exact hc hi
  · exact (Nat.prime_iff_prime_int.mp hp.out).not_dvd_one hi

theorem model_det_ne (c : ℤ) (hc : ¬ (p : ℤ) ∣ c) (σ : OddSymbol) (N : ℕ) : (model p c σ N).det ≠ 0 := by
  induction N generalizing σ with
  | zero => show (0 : Matrix (Fin 0) (Fin 0) ℤ).det ≠ 0; simp
  | succ N ih =>
    show (blk p (diagonal (unitEntries c (σ 0))) (model p c (shiftSym σ) N)).det ≠ 0
    rw [blk_det]
    have h1 := not_dvd_unitEntries_det (p := p) hc (σ 0)
    exact mul_ne_zero (fun h => h1 (by rw [h]; exact dvd_zero _))
      (mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)) (ih _))

theorem totDim_eq (σ : OddSymbol) (N : ℕ) : totDim σ N = ∑ k ∈ Finset.range N, (σ k).dim := by
  induction N generalizing σ with
  | zero => rfl
  | succ N ih => rw [totDim, ih, Finset.sum_range_succ']; simp [shiftSym]; ring

theorem padicValInt_model_det (c : ℤ) (hc : ¬ (p : ℤ) ∣ c) (σ : OddSymbol) (N : ℕ) :
    padicValInt p (model p c σ N).det = ∑ k ∈ Finset.range N, k * (σ k).dim := by
  induction N generalizing σ with
  | zero => show padicValInt p (0 : Matrix (Fin 0) (Fin 0) ℤ).det = _; simp
  | succ N ih =>
    show padicValInt p (blk p (diagonal (unitEntries c (σ 0))) (model p c (shiftSym σ) N)).det = _
    rw [blk_det]
    have h1 := not_dvd_unitEntries_det (p := p) hc (σ 0)
    have hp0 : ((p : ℤ)) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    rw [padicValInt.mul (fun h => h1 (by rw [h]; exact dvd_zero _))
        (mul_ne_zero (pow_ne_zero _ hp0) (model_det_ne c hc _ N)),
      padicValInt.eq_zero_of_not_dvd h1, zero_add,
      padicValInt.mul (pow_ne_zero _ hp0) (model_det_ne c hc _ N), ih, Finset.sum_range_succ', totDim_eq]
    have : padicValInt p ((p : ℤ) ^ (∑ k ∈ Finset.range N, (shiftSym σ k).dim)) =
        ∑ k ∈ Finset.range N, (shiftSym σ k).dim := by
      unfold padicValInt; simp
    rw [this]
    simp only [shiftSym, zero_mul, add_zero, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring

end Model

/-! ### The induction over the constituents -/

section Induction

variable {p : ℕ} [hp : Fact p.Prime]

/-- The $p$-mass of the zero-dimensional form is $1$. -/
theorem pMassDensity_fin_zero (A : Matrix (Fin 0) (Fin 0) ℤ) : pMassDensity p A = 1 := by
  have hc : ∀ r, countN p r A = 1 := fun r => by
    unfold countN
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩, ⟨⟨1, Subsingleton.elim _ _⟩⟩⟩
  have hα : alphaP p A = 1 := by
    unfold alphaP
    simp only [hc, Nat.cast_one, Nat.zero_mul, Nat.zero_div, mul_zero, pow_zero, div_one]
    exact tendsto_const_nhds.limUnder_eq
  unfold pMassDensity
  rw [hα, Matrix.det_isEmpty]
  simp

/-- The sign of the unit form $\operatorname{diag}(c_k, 1, \dots, 1)$ is the sign of the constituent, when $c$ is a
non-residue. -/
theorem sign_unitEntries_det {c : ℤ} (hc : jacobiSym c p = -1) (f : OddFactor) (hf : f.dim ≠ 0) :
    Sign.ofInt (jacobiSym (diagonal (unitEntries c f)).det p) = f.sign := by
  rw [unitEntries_det c f hf]
  cases hs : f.sign <;> simp [hc, Sign.ofInt, jacobiSym.one_left]

/-- **The unimodular constituent**: for $p$ odd, the $p$-mass of $\operatorname{diag}(c_k, 1, \dots, 1)$ is the diagonal
factor $M_p$ of its species (Table 1); by `pMassDensity_eq_stdP` it is $\mathrm{std}_p$, and by
`pMassOdd_unimodular` that is $M_p$ of the species. -/
@[kb "conwaysloane1988" "§5, p. 265 (M_p(f_q) is the p-mass of f_q, p odd)"]
theorem pMassDensity_unitEntries (hp2 : p ≠ 2) {c : ℤ} (hc : jacobiSym c p = -1) (f : OddFactor) :
    pMassDensity p (diagonal (unitEntries c f)) = ((oddSpecies p f).diagFactor p : ℝ) := by
  have hcp : ¬ (p : ℤ) ∣ c := by
    intro h
    have : jacobiSym c p = 0 := by
      rw [jacobiSym.mod_left, Int.emod_eq_zero_of_dvd h, jacobiSym.zero_left hp.out.one_lt]
    rw [this] at hc; norm_num at hc
  obtain ⟨d, sg⟩ := f
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [pMassDensity_fin_zero]
    simp [oddSpecies, Species.diagFactor]
  · have hnd := not_dvd_unitEntries_det (p := p) hcp ⟨d, sg⟩
    have hdet : (diagonal (unitEntries c ⟨d, sg⟩)).det ≠ 0 := fun h => hnd (by rw [h]; exact dvd_zero _)
    rw [pMassDensity_eq_stdP hp.out hp2 hd (diagonal_transpose _) hdet hnd,
      ← pMassOdd_unimodular hp2 hd hnd, sign_unitEntries_det hc ⟨d, sg⟩ (by simp; omega)]
    simp [pMassOdd, crossExp, unimodularSymbol]

/-- **(3) for the diagonal model** ($p$ odd): $m_p(\text{model of }\sigma) = $ the right-hand side of (3). -/
@[kb "conwaysloane1988" "(3), p. 263 (p odd, diagonal model)"]
theorem pMassDensity_model (hp2 : p ≠ 2) {c : ℤ} (hc : jacobiSym c p = -1) (σ : OddSymbol) (N : ℕ) :
    pMassDensity p (model p c σ N) = pMassOdd p σ N := by
  have hcp : ¬ (p : ℤ) ∣ c := by
    intro h
    have : jacobiSym c p = 0 := by
      rw [jacobiSym.mod_left, Int.emod_eq_zero_of_dvd h, jacobiSym.zero_left hp.out.one_lt]
    rw [this] at hc; norm_num at hc
  induction N generalizing σ with
  | zero =>
    show pMassDensity p (0 : Matrix (Fin 0) (Fin 0) ℤ) = _
    rw [pMassDensity_fin_zero]
    simp [pMassOdd, crossExp]
  | succ N ih =>
    show pMassDensity p (blk p (diagonal (unitEntries c (σ 0))) (model p c (shiftSym σ) N)) = _
    rw [pMassDensity_blk hp2 (diagonal_transpose _) (not_dvd_unitEntries_det hcp _) (model_isSymm c _ N)
      (model_det_ne c hcp _ N), pMassDensity_unitEntries hp2 hc, ih, pMassOdd_succ,
      padicValInt_model_det c hcp, totDim_eq, sqrt_pow_eq_rpow]
    have e : ∑ k ∈ Finset.range N, (shiftSym σ k).dim + ∑ k ∈ Finset.range N, k * (shiftSym σ k).dim =
        ∑ k ∈ Finset.range N, (k + 1) * (σ (k + 1)).dim := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun k _ => by simp [shiftSym]; ring
    rw [e]
    push_cast
    ring_nf

end Induction

/-! ### The symbol of the model, and the proof of `PMassFormulaOdd` -/

section Symbol

variable {p : ℕ} [hp : Fact p.Prime]

theorem not_dvd_of_jacobiSym {c : ℤ} (hc : jacobiSym c p = -1) : ¬ (p : ℤ) ∣ c := by
  intro h
  have : jacobiSym c p = 0 := by
    rw [jacobiSym.mod_left, Int.emod_eq_zero_of_dvd h, jacobiSym.zero_left hp.out.one_lt]
  rw [this] at hc; norm_num at hc

/-- There is an integer quadratic non-residue modulo an odd prime. -/
theorem exists_nonresidue (hp2 : p ≠ 2) : ∃ c : ℤ, jacobiSym c p = -1 := by
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
  refine ⟨(a.val : ℤ), ?_⟩
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_neg_one_iff]
  simpa using ha

theorem norm_intCast_eq_one {z : ℤ} (hz : ¬ (p : ℤ) ∣ z) : ‖(z : ℚ_[p])‖ = 1 := by
  have h1 : ‖(z : ℚ_[p])‖ ≤ 1 := Padic.norm_int_le_one z
  have h2 : ¬ ‖(z : ℚ_[p])‖ < 1 := fun h => hz (Padic.norm_intCast_lt_one_iff.mp h)
  linarith [not_lt.mp h2]

/-- A non-residue is not a square in $\mathbb Q_p$. -/
theorem not_isSquare_of_jacobiSym {c : ℤ} (hc : jacobiSym c p = -1) : ¬ IsSquare (c : ℚ_[p]) := by
  have hcp := not_dvd_of_jacobiSym hc
  rintro ⟨x, hx⟩
  have h1 : ‖(c : ℚ_[p])‖ = 1 := norm_intCast_eq_one hcp
  have hn : ‖x‖ = 1 := by
    rw [hx, norm_mul] at h1
    nlinarith [norm_nonneg x]
  let y : ℤ_[p] := ⟨x, (PadicInt.mem_subring_iff p).2 hn.le⟩
  have hy : (c : ℤ_[p]) = y * y := Subtype.ext (by simpa using hx)
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_neg_one_iff] at hc
  apply hc
  refine ⟨PadicInt.toZMod y, ?_⟩
  have := congrArg PadicInt.toZMod hy
  simpa using this

/-- The exponents of the diagonal model: $k$ on the constituent of scale $p^k$. -/
def modelZ (σ : OddSymbol) : (N : ℕ) → Fin (totDim σ N) → ℕ
  | 0 => Fin.elim0
  | N + 1 => Fin.append (fun _ => 0) (fun j => modelZ (shiftSym σ) N j + 1)

/-- The unit parts of the diagonal entries of the model. -/
def modelU (c : ℤ) (σ : OddSymbol) : (N : ℕ) → Fin (totDim σ N) → ℤ
  | 0 => Fin.elim0
  | N + 1 => Fin.append (unitEntries c (σ 0)) (modelU c (shiftSym σ) N)

theorem modelD_eq (c : ℤ) (σ : OddSymbol) (N : ℕ) (i : Fin (totDim σ N)) :
    modelD p c σ N i = (p : ℤ) ^ modelZ σ N i * modelU c σ N i := by
  induction N generalizing σ with
  | zero => exact i.elim0
  | succ N ih =>
    revert i
    show ∀ i : Fin ((σ 0).dim + totDim (shiftSym σ) N),
      Fin.append (unitEntries c (σ 0)) (fun j => (p : ℤ) * modelD p c (shiftSym σ) N j) i =
      (p : ℤ) ^ (Fin.append (fun _ => 0) (fun j => modelZ (shiftSym σ) N j + 1) i) *
        Fin.append (unitEntries c (σ 0)) (modelU c (shiftSym σ) N) i
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp
    · simp only [Fin.append_right, ih, pow_succ]; ring

theorem modelU_not_dvd {c : ℤ} (hc : ¬ (p : ℤ) ∣ c) (σ : OddSymbol) (N : ℕ) (i : Fin (totDim σ N)) :
    ¬ (p : ℤ) ∣ modelU c σ N i := by
  induction N generalizing σ with
  | zero => exact i.elim0
  | succ N ih =>
    revert i
    show ∀ i : Fin ((σ 0).dim + totDim (shiftSym σ) N),
      ¬ (p : ℤ) ∣ Fin.append (unitEntries c (σ 0)) (modelU c (shiftSym σ) N) i
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp only [Fin.append_left, unitEntries]
      split_ifs
      · exact hc
      · exact (Nat.prime_iff_prime_int.mp hp.out).not_dvd_one
    · simp only [Fin.append_right]; exact ih _ j

theorem sum_modelZ (σ : OddSymbol) (N k : ℕ) :
    ∑ i, (if modelZ σ N i = k then 1 else 0) = if k < N then (σ k).dim else 0 := by
  induction N generalizing σ k with
  | zero => show ∑ i : Fin 0, _ = _; simp
  | succ N ih =>
    show ∑ i : Fin ((σ 0).dim + totDim (shiftSym σ) N),
      (if Fin.append (fun _ => 0) (fun j => modelZ (shiftSym σ) N j + 1) i = k then 1 else 0) = _
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rcases k with _ | k
    · simp
    · simp only [Nat.add_right_cancel_iff, ih, shiftSym]
      simp [Nat.succ_ne_zero]

theorem prod_modelU (c : ℤ) (σ : OddSymbol) (N k : ℕ) :
    ∏ i, (if modelZ σ N i = k then (modelU c σ N i : ℚ_[p]) else 1) =
      if k < N ∧ (σ k).dim ≠ 0 ∧ (σ k).sign = .minus then (c : ℚ_[p]) else 1 := by
  induction N generalizing σ k with
  | zero => show ∏ i : Fin 0, _ = _; simp
  | succ N ih =>
    show ∏ i : Fin ((σ 0).dim + totDim (shiftSym σ) N),
      (if Fin.append (fun _ => 0) (fun j => modelZ (shiftSym σ) N j + 1) i = k then
        ((Fin.append (unitEntries c (σ 0)) (modelU c (shiftSym σ) N) i : ℤ) : ℚ_[p]) else 1) = _
    rw [Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rcases k with _ | k
    · simp only [if_true, Nat.succ_ne_zero, if_false, Finset.prod_const_one, mul_one]
      rw [← Int.cast_prod]
      by_cases hd : (σ 0).dim = 0
      · have : IsEmpty (Fin (σ 0).dim) := by rw [hd]; infer_instance
        simp [hd]
      · rw [unitEntries_prod c (σ 0) hd]
        split_ifs <;> simp_all
    · rw [Finset.prod_eq_one (fun i _ => if_neg (by omega)), one_mul]
      simp only [Nat.add_right_cancel_iff]
      rw [ih]
      simp only [shiftSym, Nat.add_lt_add_iff_right]
      congr 1

theorem card_subtype_eq_sum {m : ℕ} (z : Fin m → ℕ) (k : ℕ) :
    Fintype.card {i // z i = k} = ∑ i, (if z i = k then 1 else 0) := by
  rw [Fintype.card_subtype, Finset.card_filter]

theorem prod_subtype_eq_prod_ite {m : ℕ} (z : Fin m → ℕ) (k : ℕ) (u : Fin m → ℚ_[p]) :
    ∏ i : {i // z i = k}, u i = ∏ i, (if z i = k then u i else 1) := by
  rw [← Finset.prod_filter, ← Finset.prod_subtype (Finset.univ.filter fun i => z i = k) (by simp)]

/-- **The symbol of the diagonal model is $\sigma$** (for a symbol without zero-dimensional constituents of sign $-$,
trivial from $p^N$ on). -/
theorem isOddSymbolOf_model {c : ℤ} (hc : jacobiSym c p = -1) (σ : OddSymbol) (N : ℕ)
    (hnorm : ∀ k, (σ k).dim = 0 → (σ k).sign = .plus) (hN : ∀ k, N ≤ k → σ k = OddFactor.trivial) :
    IsOddSymbolOf p ((model p c σ N).map (Int.cast : ℤ → ℚ_[p])) σ := by
  have hcp := not_dvd_of_jacobiSym hc
  refine ⟨modelZ σ N, fun i => (modelU c σ N i : ℚ_[p]), fun i => norm_intCast_eq_one (modelU_not_dvd hcp σ N i),
    ?_, ?_⟩
  · have : (model p c σ N).map (Int.cast : ℤ → ℚ_[p]) =
        diagonal fun i => (p : ℚ_[p]) ^ modelZ σ N i * (modelU c σ N i : ℚ_[p]) := by
      rw [model_eq_diagonal, diagonal_map (Int.cast_zero)]
      congr 1; funext i; rw [modelD_eq]; push_cast; rfl
    rw [this]; exact Cassels.ZpEquiv.refl _
  · funext k
    unfold oddSymbolOfDiag
    rw [card_subtype_eq_sum, sum_modelZ,
      prod_subtype_eq_prod_ite (modelZ σ N) k (fun i => (modelU c σ N i : ℚ_[p])), prod_modelU]
    rcases lt_or_ge k N with hk | hk
    · simp only [hk, if_true, true_and]
      have hn := hnorm k
      have hnsq := not_isSquare_of_jacobiSym hc
      generalize σ k = f at *
      obtain ⟨d, sg⟩ := f
      cases sg <;> rcases Nat.eq_zero_or_pos d with rfl | hd <;>
        simp_all [IsSquare.one, Nat.pos_iff_ne_zero.mp]
    · rw [hN k hk]
      simp [show ¬ k < N by omega, OddFactor.trivial]

/-- The symbol of a diagonal form has no zero-dimensional constituent of sign $-$. -/
theorem oddSymbolOfDiag_norm {n : ℕ} (z : Fin n → ℕ) (u : Fin n → ℚ_[p]) (k : ℕ)
    (h : (oddSymbolOfDiag p z u k).dim = 0) : (oddSymbolOfDiag p z u k).sign = .plus := by
  unfold oddSymbolOfDiag at h ⊢
  have : IsEmpty {i // z i = k} := Fintype.card_eq_zero_iff.mp h
  simp

/-- The total dimension of a symbol of an $n$-dimensional form, trivial from $p^N$ on, is $n$. -/
theorem totDim_oddSymbolOfDiag {n : ℕ} (z : Fin n → ℕ) (u : Fin n → ℚ_[p]) (N : ℕ)
    (hN : ∀ k, N ≤ k → oddSymbolOfDiag p z u k = OddFactor.trivial) :
    totDim (oddSymbolOfDiag p z u) N = n := by
  have hz : ∀ i, z i < N := by
    intro i
    by_contra h
    have := congrArg OddFactor.dim (hN (z i) (by omega))
    simp only [oddSymbolOfDiag, OddFactor.trivial] at this
    exact (Fintype.card_eq_zero_iff.mp this).false ⟨i, rfl⟩
  rw [totDim_eq]
  simp only [oddSymbolOfDiag, Fintype.card_subtype]
  rw [← Finset.card_eq_sum_card_fiberwise (f := z) (s := Finset.univ) (t := Finset.range N)
    (fun i _ => Finset.mem_range.mpr (hz i))]
  simp

/-- **Formula (3) at an odd prime** (Conway–Sloane 1988, (3), p. 263, with Tables 1 and 2): for every symmetric
integral Gram matrix $A$ with $\det A \ne 0$ and every $p$-adic symbol $\sigma$ of $A$ (trivial from $p^N$ on), the
$p$-mass of §12 equals the right-hand side of (3):
$$\frac{p^{s(n+1)/2}}{\alpha_p(A)} = \prod_q M_p(f_q)\cdot\prod_{q<q'}(q'/q)^{\frac12n(q)n(q')}.$$
Unconditional: this proves the former named input `PMassFormulaOdd p`. The paper cites it (Smith, Minkowski, Siegel,
Watson) without proof. -/
@[kb "conwaysloane1988" "(3), p. 263 (p odd); Tables 1–2, p. 264"]
theorem pMassFormulaOdd (hp2 : p ≠ 2) : PMassFormulaOdd p := by
  refine ⟨fun {n} A hA hdet σ N hσ hN => ?_⟩
  obtain ⟨c, hc⟩ := exists_nonresidue (p := p) hp2
  have hcp := not_dvd_of_jacobiSym hc
  obtain ⟨z, u, -, -, hσz⟩ := id hσ
  have hnorm : ∀ k, (σ k).dim = 0 → (σ k).sign = .plus := by
    rw [hσz]; exact oddSymbolOfDiag_norm z u
  have hdim : totDim σ N = n := by
    subst hσz; exact totDim_oddSymbolOfDiag z u N hN
  clear hσz z u
  subst hdim
  have hM := isOddSymbolOf_model hc σ N hnorm hN
  have hZ := zpEquiv_of_oddSymbol_eq hp2 hσ hM
  rw [← pMassDensity_eq_of_zpEquiv hZ hdet (model_det_ne c hcp σ N), pMassDensity_model hp2 hc]

end Symbol

end QuadFormsKB.ConwaySloane.Mass
