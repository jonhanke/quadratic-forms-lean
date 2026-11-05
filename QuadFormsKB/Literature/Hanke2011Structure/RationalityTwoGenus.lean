/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.Dyadic7Classify
import QuadFormsKB.Tamagawa.Dyadic7Hasse
import QuadFormsKB.Tamagawa.Dyadic7Beta
import QuadFormsKB.Literature.Hanke2011Structure.LocalMassDensity
import QuadFormsKB.Literature.Hanke2011Structure.RationalityTwoBlocks
import QuadFormsKB.Literature.Hanke2011Structure.RationalityTwoFinite

/-!
# Paper 6, Theorem 5.4 at $p = 2$: local genera glued across a gap

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (`hanke2011structure`), Thm. 5.4, proof, p. 24.

Let $v$ be the prime of $\mathbb Q$ above $2$.  Every nondegenerate local genus $G$ in $n$ variables is the genus of
$Q_D = \tfrac12x^{\mathsf T}H_Dx$ for an admissible list $D$ of Cassels' blocks (`Dyadic7.exists_genusOf`); we fix one,
`rep G`, and read off:

* the *profile* `dG G k`: the dimension of the Jordan constituent of scale $2^k$ of $H_D$ (independent of $D$, by
  Conway–Sloane's Theorem 10, `Dyadic7.genusOf_eq_iff`);
* $\nu(G) = \operatorname{ord}_2\det H$ (`νG`), the unit class $u(G) \in \mathbb Z/8$ of $\det H$ (`uG`), the Hasse
  invariant, and the *state* `st G` $= (\nu \bmod 2, u, c_2)$;
* the *cut* `cutG G`: the first scale $2^c$ above the bottom of the profile with $n_c = n_{c+1} = 0$.

`glueN n P T` is the genus of $Q_{D_P} \perp Q_{D_T}$.  If $P$ lives below the scale $2^c$ and $T$ above
$2^{c+1}$:
* its state is $(\nu_P + \nu_T,\ u_Pu_T,\ c_Pc_T\cdot\mathrm{crossSign})$ (`st_glueN`);
* its inverse density is $\beta(P)^{-1}\beta(T)^{-1}2^{pq - 1 - \nu_Pq}$ (`invBeta_glueN`, from the 2-mass formula
  `Two.pMassFormulaTwo_holds` and the gluing of 2-masses `pMassTwo_glue`);
* its bottom piece and top piece are $P$ and $T$ again (`bottom_glueN`, `top_glueN`), and every genus with a gap is
  glued from its bottom and top pieces (`glueN_bottom_top`).

`Sh2 T` is the genus of $4Q_{D_T}$ (all scales raised by two): same state, $\nu$ raised by $2q$, inverse density divided
by $2^{q(q+1)}$, and $T \mapsto$ `Sh2 T` is injective (`Sh2_injective`).

Indices are 0-based.
-/

open IsDedekindDomain NumberField Matrix Finset

namespace QuadFormsKB.Hanke2011Structure.RatTwo

open QuadFormsKB.ConwaySloane QuadFormsKB.ConwaySloane.Mass QuadFormsKB.Dyadic7 Cassels
  QuadFormsKB.Hanke2011Structure

noncomputable section

variable {v : HeightOneSpectrum (𝓞 ℚ)}

/-! ### Representatives -/

/-- $D$ represents the genus $G$: admissible, $n$ variables, genus of $Q_D$ equal to $G$. -/
def IsRep {n : ℕ} (G : LocGenus v n) (D : List DyBlock) : Prop := AdmL D ∧ dyDim D = n ∧ genusOf v n D = G

open Classical in
/-- A fixed representing block list of a genus (`[]` if there is none). -/
def rep {n : ℕ} (G : LocGenus v n) : List DyBlock := if h : ∃ D, IsRep G D then h.choose else []

theorem isRep_rep (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {n : ℕ} {G : LocGenus v n} (hN : G.Nondeg) : IsRep G (rep G) := by
  have h : ∃ D, IsRep G D := by
    obtain ⟨D, hD, h0, hn, hev, rfl⟩ := exists_genusOf v h2 G hN
    exact ⟨D, ⟨hD, h0, hev⟩, hn, rfl⟩
  unfold rep; rw [dif_pos h]; exact h.choose_spec

theorem isRep_genusOf {n : ℕ} {D : List DyBlock} (hD : AdmL D) (hn : dyDim D = n) : IsRep (genusOf v n D) D :=
  ⟨hD, hn, rfl⟩

theorem IsRep.nondeg {n : ℕ} {G : LocGenus v n} {D : List DyBlock} (h : IsRep G D) : G.Nondeg := by
  rw [← h.2.2]; exact nondeg_genusOf v h.1.1 h.1.2.1 h.2.1 h.1.2.2

theorem genusOf_eq_iff' (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {n : ℕ} {A B : List DyBlock} (hA : AdmL A) (hB : AdmL B)
    (hnA : dyDim A = n) (hnB : dyDim B = n) :
    genusOf v n A = genusOf v n B ↔ MoveEquiv (blockSymbol A) (blockSymbol B) :=
  genusOf_eq_iff v h2 hA.1 hA.2.1 hnA hA.2.2 hB.1 hB.2.1 hnB hB.2.2

theorem IsRep.moveEquiv (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {n : ℕ} {G : LocGenus v n} {D D' : List DyBlock}
    (h : IsRep G D) (h' : IsRep G D') : MoveEquiv (blockSymbol D) (blockSymbol D') :=
  (genusOf_eq_iff' h2 h.1 h'.1 h.2.1 h'.2.1).1 (h.2.2.trans h'.2.2.symm)

/-! ### Blocks and the constituents of the symbol -/

theorem dim_blockSymbol_ne_zero_iff (D : List DyBlock) (k : ℕ) :
    (blockSymbol D k).dim ≠ 0 ↔ ∃ b ∈ D, blockExp b = k := by
  simp only [blockSymbol, ne_eq]
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    apply h
    rw [List.filter_eq_nil_iff.2 (fun b hb hbk => hn b hb (by simpa using hbk))]
    rfl
  · rintro ⟨b, hb, hbk⟩ h0
    have hmem : b ∈ D.filter fun b => decide (blockExp b = (k : ℤ)) := List.mem_filter.2 ⟨hb, by simpa using hbk⟩
    have h1 : b.dim ∈ (D.filter fun b => decide (blockExp b = (k : ℤ))).map DyBlock.dim := List.mem_map_of_mem hmem
    have h2 := List.le_sum_of_mem h1
    have h3 : 1 ≤ b.dim := by cases b <;> simp [DyBlock.dim]
    omega

theorem isTypeI_blockSymbol_iff (D : List DyBlock) (k : ℕ) :
    IsTypeI (blockSymbol D) k ↔ ∃ b ∈ D, blockExp b = k ∧ IsSqBlock b := by
  unfold IsTypeI blockSymbol
  simp only
  split_ifs with h
  · simp only [true_iff]
    obtain ⟨b, hb, hsq⟩ := List.any_eq_true.1 h
    obtain ⟨hbD, hbk⟩ := List.mem_filter.1 hb
    exact ⟨b, hbD, by simpa using hbk, by simpa using hsq⟩
  · simp only [reduceCtorEq, false_iff]
    rintro ⟨b, hbD, hbk, hsq⟩
    apply h
    exact List.any_eq_true.2 ⟨b, List.mem_filter.2 ⟨hbD, by simpa using hbk⟩, by simpa using hsq⟩

theorem not_isTypeI_of_dim_zero {D : List DyBlock} {k : ℕ} (h : (blockSymbol D k).dim = 0) :
    ¬ IsTypeI (blockSymbol D) k := by
  rw [isTypeI_blockSymbol_iff]
  rintro ⟨b, hb, hbk, -⟩
  exact (dim_blockSymbol_ne_zero_iff D k).2 ⟨b, hb, hbk⟩ h

theorem blockSymbol_eq_trivial_of_dim {D : List DyBlock} {k : ℕ} (h : (blockSymbol D k).dim = 0) :
    blockSymbol D k = TwoFactor.trivial := by
  refine blockSymbol_of_nil (List.filter_eq_nil_iff.2 fun b hb hbk => ?_)
  exact (dim_blockSymbol_ne_zero_iff D k).2 ⟨b, hb, by simpa using hbk⟩ h

theorem exp_nat {D : List DyBlock} (h0 : ∀ b ∈ D, 0 ≤ blockExp b) {b : DyBlock} (hb : b ∈ D) :
    ∃ k : ℕ, blockExp b = k := ⟨(blockExp b).toNat, by have := h0 b hb; omega⟩

theorem blockSymbol_supported (D : List DyBlock) (h0 : ∀ b ∈ D, 0 ≤ blockExp b) :
    ∃ N : ℕ, (blockSymbol D).SupportedBelow N :=
  ⟨(D.map fun b => (blockExp b).toNat).sum + 1, blockSymbol_supportedBelow h0 fun b hb =>
    Nat.lt_succ_of_le (List.le_sum_of_mem (List.mem_map_of_mem hb))⟩

/-- Two admissible lists related by moves have the same rank. -/
theorem dyDim_eq_of_moveEquiv {A B : List DyBlock} (hA : AdmL A) (hB : AdmL B)
    (h : MoveEquiv (blockSymbol A) (blockSymbol B)) : dyDim A = dyDim B := by
  obtain ⟨N, hN⟩ := blockSymbol_supported A hA.2.1
  obtain ⟨M, hM⟩ := blockSymbol_supported B hB.2.1
  have bound : ∀ (D : List DyBlock) (L : ℕ), (blockSymbol D).SupportedBelow L → ∀ b ∈ D,
      blockExp b < (max N M : ℕ) ∨ True := fun _ _ _ _ _ => Or.inr trivial
  have hbA : ∀ b ∈ A, blockExp b < (max N M : ℕ) := by
    intro b hb
    obtain ⟨k, hk⟩ := exp_nat hA.2.1 hb
    rw [hk]
    by_contra hc
    have := hN k (by push_cast at hc; omega)
    exact (dim_blockSymbol_ne_zero_iff A k).2 ⟨b, hb, hk⟩ (by rw [this]; rfl)
  have hbB : ∀ b ∈ B, blockExp b < (max N M : ℕ) := by
    intro b hb
    obtain ⟨k, hk⟩ := exp_nat hB.2.1 hb
    rw [hk]
    by_contra hc
    have := hM k (by push_cast at hc; omega)
    exact (dim_blockSymbol_ne_zero_iff B k).2 ⟨b, hb, hk⟩ (by rw [this]; rfl)
  rw [dyDim_eq_sum hA.2.1 hbA, dyDim_eq_sum hB.2.1 hbB]
  exact Finset.sum_congr rfl fun k _ => (h.sameInvariants.dim_eq k).symm

/-! ### Invariants of a genus -/

/-- The **profile** of a genus: the dimension of the Jordan constituent of scale $2^k$. -/
def dG {n : ℕ} (G : LocGenus v n) (k : ℕ) : ℕ := (blockSymbol (rep G) k).dim

/-- $\nu(G) = \operatorname{ord}_2\det H$. -/
def νG {n : ℕ} (G : LocGenus v n) : ℕ := valSum (rep G)

/-- The unit class of $\det H$ modulo $8$. -/
def uG {n : ℕ} (G : LocGenus v n) : ZMod 8 := ((unitProd (rep G) : ℤ) : ZMod 8)

/-- The **state** of a genus: $(\nu \bmod 2,\ u \bmod 8,\ c_2)$. -/
abbrev State : Type := ZMod 2 × ZMod 8 × ℤ

/-- See `State`. -/
def st {n : ℕ} (G : LocGenus v n) : State := ((νG G : ZMod 2), uG G, G.hasse)

section Rep

variable (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
include h2

theorem IsRep.dim_eq {n : ℕ} {G : LocGenus v n} {D : List DyBlock} (h : IsRep G D) (k : ℕ) :
    (blockSymbol D k).dim = dG G k :=
  ((h.moveEquiv h2 (isRep_rep h2 h.nondeg)).sameInvariants.dim_eq k).symm

theorem IsRep.isTypeI_iff {n : ℕ} {G : LocGenus v n} {D : List DyBlock} (h : IsRep G D) (k : ℕ) :
    IsTypeI (blockSymbol D) k ↔ IsTypeI (blockSymbol (rep G)) k :=
  (MoveEquiv.isTypeI_iff (h.moveEquiv h2 (isRep_rep h2 h.nondeg)) k).symm

theorem IsRep.det {n : ℕ} {G : LocGenus v n} {D : List DyBlock} (h : IsRep G D) :
    G.det = zSqCl v (2 ^ valSum D * unitProd D) := by
  rw [← h.2.2]; exact det_genusOf v h.1.1 h.1.2.1 h.2.1 h.1.2.2

omit h2 in
theorem odd_unitProd' {D : List DyBlock} (hD : AdmL D) : Odd (unitProd D) :=
  Int.not_even_iff_odd.mp fun he => odd_unitProd D hD.1 (even_iff_two_dvd.mp he)

theorem IsRep.valSum_eq {n : ℕ} {G : LocGenus v n} {D : List DyBlock} (h : IsRep G D) : valSum D = νG G := by
  have h' := isRep_rep h2 h.nondeg
  have e := (h.det h2).symm.trans (h'.det h2)
  have := congrArg (SqCl.ordZ (localOrd v) (localUnits_le_ker v)) e
  rw [ordZ_zSqCl v h2 _ (odd_unitProd' h.1), ordZ_zSqCl v h2 _ (odd_unitProd' h'.1)] at this
  exact_mod_cast this

theorem IsRep.unit_eq {n : ℕ} {G : LocGenus v n} {D : List DyBlock} (h : IsRep G D) :
    ((unitProd D : ℤ) : ZMod 8) = uG G := by
  have h' := isRep_rep h2 h.nondeg
  have e := (h.det h2).symm.trans (h'.det h2)
  rw [h.valSum_eq h2, ← h'.valSum_eq h2, zSqCl_eq_iff v h2 _ (odd_unitProd' h.1) (odd_unitProd' h'.1)] at e
  unfold uG
  exact (ZMod.intCast_eq_intCast_iff' _ _ 8).2 e

theorem IsRep.hasse_eq {n : ℕ} {G : LocGenus v n} {D : List DyBlock} (h : IsRep G D) : G.hasse = hasseQ D := by
  rw [← h.2.2]; exact hasse_genusOf v h2 h.1.1 h.1.2.1 h.2.1 h.1.2.2

theorem IsRep.det_eq_iff {n : ℕ} {G : LocGenus v n} {D : List DyBlock} (h : IsRep G D) {w : ℤ} (hw : Odd w)
    (ν : ℕ) : G.det = zSqCl v (2 ^ ν * w) ↔ νG G = ν ∧ uG G = ((w : ℤ) : ZMod 8) := by
  rw [h.det h2, ← h.valSum_eq h2, ← h.unit_eq h2]
  constructor
  · intro e
    have := congrArg (SqCl.ordZ (localOrd v) (localUnits_le_ker v)) e
    rw [ordZ_zSqCl v h2 _ (odd_unitProd' h.1), ordZ_zSqCl v h2 _ hw] at this
    have hν : valSum D = ν := by exact_mod_cast this
    rw [hν, zSqCl_eq_iff v h2 _ (odd_unitProd' h.1) hw] at e
    exact ⟨hν, (ZMod.intCast_eq_intCast_iff' _ _ 8).2 e⟩
  · rintro ⟨hν, hu⟩
    rw [hν, zSqCl_eq_iff v h2 _ (odd_unitProd' h.1) hw]
    exact (ZMod.intCast_eq_intCast_iff' _ _ 8).1 hu

theorem IsRep.st_eq {n : ℕ} {G : LocGenus v n} {D : List DyBlock} (h : IsRep G D) :
    st G = ((valSum D : ZMod 2), ((unitProd D : ℤ) : ZMod 8), hasseQ D) := by
  unfold st; rw [h.valSum_eq h2, h.unit_eq h2, h.hasse_eq h2]

/-- Exponents of a representing list lie in the support of the profile. -/
theorem IsRep.exp_mem {n : ℕ} {G : LocGenus v n} {D : List DyBlock} (h : IsRep G D) {b : DyBlock} (hb : b ∈ D) :
    ∃ k : ℕ, blockExp b = k ∧ dG G k ≠ 0 := by
  obtain ⟨k, hk⟩ := exp_nat h.1.2.1 hb
  exact ⟨k, hk, by rw [← h.dim_eq h2]; exact (dim_blockSymbol_ne_zero_iff D k).2 ⟨b, hb, hk⟩⟩

end Rep

/-! ### The inverse density -/

theorem sqrt_two_pow_mul (a : ℕ) : Real.sqrt 2 ^ (2 * a) = (2 : ℝ) ^ a := by
  rw [pow_mul, Real.sq_sqrt (by norm_num)]

theorem rpow_half (m : ℕ) : (2 : ℝ) ^ ((m : ℝ) / 2) = Real.sqrt 2 ^ m := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  congr 1; ring

theorem two_pow_half_nat (n : ℕ) : (2 : ℝ) ^ (n * (n + 1) / 2) = Real.sqrt 2 ^ (n * (n + 1)) := by
  obtain ⟨k, hk⟩ : Even (n * (n + 1)) := Nat.even_mul_succ_self n
  rw [hk, show (k + k) / 2 = k by omega, show k + k = 2 * k by ring, sqrt_two_pow_mul]

/-- **The inverse density of a block genus from the 2-mass** (Conway–Sloane's formula (3), proved):
$\beta(G_D)^{-1} = 2\,\sqrt2^{\,n(n+1)}\,m_2(\sigma_D)/\sqrt2^{\,\nu(n+1)}$. -/
theorem invBeta_genusOf (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {n : ℕ} {D : List DyBlock} (hD : AdmL D) (hn : dyDim D = n)
    {N : ℕ} (hN : (blockSymbol D).SupportedBelow N) :
    ((genusOf v n D).beta)⁻¹ =
      2 * Real.sqrt 2 ^ (n * (n + 1)) * pMassTwo (blockSymbol D) N / Real.sqrt 2 ^ (valSum D * (n + 1)) := by
  rw [beta_genusOf v h2 hD.1 hD.2.1 hn hD.2.2,
    alphaP_eq_div_pMassDensity (hessZ_isSymm hn) (det_hessZ_ne_zero hD.1 hD.2.1 hn),
    Two.pMassFormulaTwo_holds.pMass_eq _ (hessZ_isSymm hn) (det_hessZ_ne_zero hD.1 hD.2.1 hn) _ N
      (isTwoSymbolOf_hessZ hD.1 hD.2.1 hn) hN,
    padicValInt_det_hessZ hD.1 hD.2.1 hn]
  have e : ((valSum D : ℕ) : ℝ) * ((n : ℝ) + 1) / 2 = (((valSum D * (n + 1) : ℕ) : ℝ)) / 2 := by push_cast; ring
  rw [e, rpow_half]
  rw [one_div, inv_pow, ← two_pow_half_nat]
  have hm : pMassTwo (blockSymbol D) N ≠ 0 ∨ pMassTwo (blockSymbol D) N = 0 := by tauto
  have hs : Real.sqrt 2 ^ (valSum D * (n + 1)) ≠ 0 := pow_ne_zero _ (by positivity)
  have hp : (0 : ℝ) < 2 ^ (n * (n + 1) / 2) := by positivity
  rcases hm with hm | hm
  · field_simp
  · simp [hm]

/-! ### Gluing genera -/

/-- **The glued genus** $P \perp T$: the genus of $Q_{D_P} \perp Q_{D_T}$ in $n$ variables. -/
def glueN (n : ℕ) {p q : ℕ} (P : LocGenus v p) (T : LocGenus v q) : LocGenus v n :=
  genusOf v n (rep P ++ rep T)

/-- The genus $4\,T$: every scale raised by two. -/
def Sh2 {q : ℕ} (T : LocGenus v q) : LocGenus v q := genusOf v q (shiftL (shiftL (rep T)))

/-- The profile vanishes below the scale $2^m$. -/
def ZeroBelow {n : ℕ} (G : LocGenus v n) (m : ℕ) : Prop := ∀ k < m, dG G k = 0

/-- The profile vanishes from the scale $2^c$ on. -/
def ZeroFrom {n : ℕ} (G : LocGenus v n) (c : ℕ) : Prop := ∀ k, c ≤ k → dG G k = 0

theorem sum_range_lt_eq {N : ℕ} (f : ℕ → ℕ → ℕ) (hf : ∀ k k', k' ≤ k → f k k' = 0) :
    ∑ k' ∈ range N, ∑ k ∈ range k', f k k' = ∑ k' ∈ range N, ∑ k ∈ range N, f k k' := by
  refine Finset.sum_congr rfl fun k' hk' => ?_
  refine Finset.sum_subset (Finset.range_subset_range.2 (Finset.mem_range.1 hk').le) fun k _ hk => ?_
  exact hf k k' (by simpa using hk)

/-- The mixed cross exponent in terms of ranks and weighted scales:
$\mathrm{mix} + \nu_a r_b = r_a\nu_b$ when the support of $a$ lies below that of $b$. -/
theorem mixExp_add {a b : ℕ → ℕ} {N : ℕ} (hab : ∀ k k', k' ≤ k → a k * b k' = 0) :
    mixExp a b N + (∑ k ∈ range N, k * a k) * (∑ k ∈ range N, b k) =
      (∑ k ∈ range N, a k) * (∑ k ∈ range N, k * b k) := by
  unfold mixExp
  have h1 : (∑ k ∈ range N, k * a k) * (∑ k ∈ range N, b k) =
      ∑ k' ∈ range N, ∑ k ∈ range N, k * a k * b k' := by
    rw [Finset.sum_mul_sum, Finset.sum_comm]
  have h2 : (∑ k ∈ range N, a k) * (∑ k ∈ range N, k * b k) =
      ∑ k' ∈ range N, ∑ k ∈ range N, a k * (k' * b k') := by
    rw [Finset.sum_mul_sum, Finset.sum_comm]
  rw [sum_range_lt_eq (fun k k' => (k' - k) * a k * b k') (fun k k' h => by
      rw [mul_assoc, hab k k' h, mul_zero]), h1, h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k' _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : k' ≤ k
  · have := hab k k' h
    have e1 : ∀ c, c * a k * b k' = c * (a k * b k') := fun c => by ring
    rw [e1, e1, this, show a k * (k' * b k') = k' * (a k * b k') by ring, this]
    simp
  · have : k' - k + k = k' := by omega
    calc (k' - k) * a k * b k' + k * a k * b k' = (k' - k + k) * a k * b k' := by ring
      _ = a k * (k' * b k') := by rw [this]; ring

theorem valSum_eq_sum {D : List DyBlock} (h0 : ∀ b ∈ D, 0 ≤ blockExp b) {N : ℕ}
    (hN : ∀ b ∈ D, blockExp b < N) : valSum D = ∑ k ∈ range N, k * (blockSymbol D k).dim := by
  induction D with
  | nil => simp [valSum, blockSymbol]
  | cons b D ih =>
    have hb0 := h0 b (List.mem_cons_self ..)
    have hbN := hN b (List.mem_cons_self ..)
    have ih' := ih (fun c hc => h0 c (List.mem_cons_of_mem _ hc)) (fun c hc => hN c (List.mem_cons_of_mem _ hc))
    have hv : valSum (b :: D) = b.dim * (blockExp b).toNat + valSum D := by simp [valSum]
    rw [hv, ih']
    have e : ∀ k, (blockSymbol (b :: D) k).dim = (if blockExp b = (k : ℤ) then b.dim else 0) +
        (blockSymbol D k).dim := by
      intro k
      simp only [blockSymbol, List.filter_cons]
      split_ifs with h1 h2 h2
      · simp
      · simp at h1; exact absurd h1 h2
      · simp at h1; exact absurd h2 h1
      · simp
    simp only [e, mul_add, Finset.sum_add_distrib]
    congr 1
    obtain ⟨m, hm⟩ : ∃ m : ℕ, blockExp b = m := ⟨(blockExp b).toNat, by omega⟩
    have hmN : m < N := by rw [hm] at hbN; exact_mod_cast hbN
    rw [Finset.sum_eq_single m]
    · simp [hm]; ring
    · intro k _ hk; rw [if_neg, mul_zero]; rw [hm]; exact_mod_cast fun (h : m = k) => hk h.symm
    · intro h; exact absurd (Finset.mem_range.2 hmN) h

section Glue

variable (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
include h2

theorem isRep_glueN {n p q : ℕ} {P : LocGenus v p} {T : LocGenus v q} (hP : P.Nondeg) (hT : T.Nondeg)
    (hn : p + q = n) : IsRep (glueN n P T) (rep P ++ rep T) := by
  have a := isRep_rep h2 hP
  have b := isRep_rep h2 hT
  exact ⟨a.1.append b.1, by rw [dyDim_append, a.2.1, b.2.1, hn], rfl⟩

theorem exps_low {n : ℕ} {P : LocGenus v n} {D : List DyBlock} (hD : IsRep P D) {c : ℕ} (hc : ZeroFrom P c) :
    ∀ b ∈ D, blockExp b ≤ c := by
  intro b hb
  obtain ⟨k, hk, hne⟩ := hD.exp_mem h2 hb
  rw [hk]
  by_contra h
  exact hne (hc k (by push_cast at h; omega))

theorem exps_high {n : ℕ} {T : LocGenus v n} {D : List DyBlock} (hD : IsRep T D) {c : ℕ}
    (hc : ZeroBelow T (c + 2)) : ∀ b ∈ D, (c : ℤ) < blockExp b := by
  intro b hb
  obtain ⟨k, hk, hne⟩ := hD.exp_mem h2 hb
  rw [hk]
  by_contra h
  exact hne (hc k (by push_cast at h; omega))

theorem blockSymbol_glue {p q : ℕ} {P : LocGenus v p} {T : LocGenus v q} (hP : P.Nondeg) (hT : T.Nondeg)
    {c : ℕ} (hPc : ZeroFrom P c) (hTc : ZeroBelow T (c + 2)) :
    blockSymbol (rep P ++ rep T) = glueS c (blockSymbol (rep P)) (blockSymbol (rep T)) :=
  blockSymbol_append (exps_low h2 (isRep_rep h2 hP) hPc) (exps_high h2 (isRep_rep h2 hT) hTc)

theorem trivial_of_zeroFrom {n : ℕ} {P : LocGenus v n} (hP : P.Nondeg) {c : ℕ} (hPc : ZeroFrom P c) :
    ∀ k, c ≤ k → blockSymbol (rep P) k = TwoFactor.trivial :=
  fun k hk => blockSymbol_eq_trivial_of_dim (hPc k hk)

theorem trivial_of_zeroBelow {n : ℕ} {T : LocGenus v n} (hT : T.Nondeg) {c : ℕ} (hTc : ZeroBelow T (c + 2)) :
    ∀ k, k ≤ c + 1 → blockSymbol (rep T) k = TwoFactor.trivial :=
  fun k hk => blockSymbol_eq_trivial_of_dim (hTc k (by omega))

theorem dG_glueN {n p q : ℕ} {P : LocGenus v p} {T : LocGenus v q} (hP : P.Nondeg) (hT : T.Nondeg)
    (hn : p + q = n) {c : ℕ} (hPc : ZeroFrom P c) (hTc : ZeroBelow T (c + 2)) (k : ℕ) :
    dG (glueN n P T) k = dG P k + dG T k := by
  rw [← (isRep_glueN h2 hP hT hn).dim_eq h2, blockSymbol_glue h2 hP hT hPc hTc]
  unfold glueS dG
  split_ifs with hk
  · rw [trivial_of_zeroBelow h2 hT hTc k (by omega)]; simp [TwoFactor.trivial]
  · rw [trivial_of_zeroFrom h2 hP hPc k (by omega)]; simp [TwoFactor.trivial]

/-- **The state of a glued genus.** -/
theorem st_glueN {n p q : ℕ} {P : LocGenus v p} {T : LocGenus v q} (hP : P.Nondeg) (hT : T.Nondeg)
    (hn : p + q = n) :
    st (glueN n P T) = ((νG P : ZMod 2) + (νG T : ZMod 2), uG P * uG T,
      P.hasse * T.hasse * crossSign (νG P) p (uG P) (νG T) q (uG T)) := by
  have a := isRep_rep h2 hP
  have b := isRep_rep h2 hT
  rw [(isRep_glueN h2 hP hT hn).st_eq h2, valSum_append, unitProd_append, hasseQ_append a.1 b.1, a.hasse_eq h2,
    b.hasse_eq h2, a.2.1, b.2.1]
  unfold νG uG
  push_cast
  rfl

/-- **The inverse density of a glued genus**:
$\beta(P \perp T)^{-1}\cdot 2\cdot 2^{\nu_Pq} = \beta(P)^{-1}\beta(T)^{-1}\cdot 2^{pq}$. -/
theorem invBeta_glueN {n p q : ℕ} {P : LocGenus v p} {T : LocGenus v q} (hP : P.Nondeg) (hT : T.Nondeg)
    (hn : p + q = n) {c : ℕ} (hPc : ZeroFrom P c) (hTc : ZeroBelow T (c + 2)) :
    ((glueN n P T).beta)⁻¹ * 2 * 2 ^ (νG P * q) = (P.beta)⁻¹ * (T.beta)⁻¹ * 2 ^ (p * q) := by
  have a := isRep_rep h2 hP
  have b := isRep_rep h2 hT
  have g := isRep_glueN h2 hP hT hn
  obtain ⟨NA, hNA⟩ := blockSymbol_supported (rep P) a.1.2.1
  obtain ⟨NB, hNB⟩ := blockSymbol_supported (rep T) b.1.2.1
  set N := max (max NA NB) (c + 2) with hNdef
  have hA : (blockSymbol (rep P)).SupportedBelow N := fun k hk => hNA k (by omega)
  have hB : (blockSymbol (rep T)).SupportedBelow N := fun k hk => hNB k (by omega)
  have hG : (blockSymbol (rep P ++ rep T)).SupportedBelow N := by
    intro k hk
    rw [blockSymbol_glue h2 hP hT hPc hTc]
    unfold glueS
    split_ifs
    · exact hA k hk
    · exact hB k hk
  have iP := invBeta_genusOf h2 a.1 a.2.1 hA
  have iT := invBeta_genusOf h2 b.1 b.2.1 hB
  rw [a.2.2] at iP
  rw [b.2.2] at iT
  rw [show glueN n P T = genusOf v n (rep P ++ rep T) from rfl, invBeta_genusOf h2 g.1 g.2.1 hG,
    iP, iT, blockSymbol_glue h2 hP hT hPc hTc,
    pMassTwo_glue (trivial_of_zeroFrom h2 hP hPc) (trivial_of_zeroBelow h2 hT hTc), valSum_append]
  -- the exponent identity
  have hbA : ∀ x ∈ rep P, blockExp x < N := by
    intro x hx
    obtain ⟨k, hk, hne⟩ := a.exp_mem h2 hx
    rw [hk]; by_contra hc'
    exact hne (by rw [← a.dim_eq h2, hA k (by push_cast at hc'; omega)]; rfl)
  have hbB : ∀ x ∈ rep T, blockExp x < N := by
    intro x hx
    obtain ⟨k, hk, hne⟩ := b.exp_mem h2 hx
    rw [hk]; by_contra hc'
    exact hne (by rw [← b.dim_eq h2, hB k (by push_cast at hc'; omega)]; rfl)
  have hmix := mixExp_add (a := fun k => (blockSymbol (rep P) k).dim) (b := fun k => (blockSymbol (rep T) k).dim)
    (N := N) (fun k k' hkk' => by
      by_cases hk : c ≤ k
      · rw [trivial_of_zeroFrom h2 hP hPc k hk]; simp [TwoFactor.trivial]
      · rw [trivial_of_zeroBelow h2 hT hTc k' (by omega)]; simp [TwoFactor.trivial])
  rw [← dyDim_eq_sum a.1.2.1 hbA, ← dyDim_eq_sum b.1.2.1 hbB, ← valSum_eq_sum a.1.2.1 hbA,
    ← valSum_eq_sum b.1.2.1 hbB, a.2.1, b.2.1] at hmix
  rw [a.valSum_eq h2] at hmix ⊢
  set M := mixExp (fun k => (blockSymbol (rep P) k).dim) (fun k => (blockSymbol (rep T) k).dim) N
  set νP := νG P
  set νT := valSum (rep T)
  set mP := pMassTwo (blockSymbol (rep P)) N
  set mT := pMassTwo (blockSymbol (rep T)) N
  subst hn
  have s2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have key : (p + q) * (p + q + 1) + M + 2 * (νP * q) + (νP * (p + 1) + νT * (q + 1)) =
      p * (p + 1) + q * (q + 1) + 2 * (p * q) + (νP + νT) * (p + q + 1) := by nlinarith [hmix]
  have hs : ∀ m : ℕ, Real.sqrt 2 ^ m ≠ 0 := fun m => pow_ne_zero _ (by positivity)
  rw [← sqrt_two_pow_mul, ← sqrt_two_pow_mul]
  field_simp
  have e1 : Real.sqrt 2 ^ ((p + q) * (p + q + 1)) * Real.sqrt 2 ^ M * Real.sqrt 2 ^ (2 * (νP * q)) *
      (Real.sqrt 2 ^ (νP * (p + 1)) * Real.sqrt 2 ^ (νT * (q + 1))) =
      Real.sqrt 2 ^ (p * (p + 1)) * Real.sqrt 2 ^ (q * (q + 1)) * Real.sqrt 2 ^ (2 * (p * q)) *
        Real.sqrt 2 ^ ((νP + νT) * (p + q + 1)) := by
    simp only [← pow_add]; rw [key]
  linear_combination (mP * mT) * e1

/-- **The bottom and top pieces of a glued genus are the pieces glued.** -/
theorem moveEquiv_low_glue {n p q : ℕ} {P : LocGenus v p} {T : LocGenus v q} (hP : P.Nondeg) (hT : T.Nondeg)
    (hn : p + q = n) {c : ℕ} (hPc : ZeroFrom P c) (hTc : ZeroBelow T (c + 2)) :
    MoveEquiv (blockSymbol (lowL c (rep (glueN n P T)))) (blockSymbol (rep P)) ∧
      MoveEquiv (blockSymbol (highL c (rep (glueN n P T)))) (blockSymbol (rep T)) := by
  have g := isRep_glueN h2 hP hT hn
  have hg := isRep_rep h2 g.nondeg
  have hme := hg.moveEquiv h2 g
  have hgap : GapAt c (blockSymbol (rep (glueN n P T))) := by
    refine ⟨not_isTypeI_of_dim_zero ?_, not_isTypeI_of_dim_zero ?_⟩ <;>
      rw [show (blockSymbol (rep (glueN n P T)) _).dim = dG (glueN n P T) _ from rfl,
        dG_glueN h2 hP hT hn hPc hTc, hPc _ (by omega), hTc _ (by omega)]
  obtain ⟨h1, h3⟩ := moveEquiv_split hme hgap
  rw [blockSymbol_lowL, blockSymbol_highL]
  rw [blockSymbol_glue h2 hP hT hPc hTc] at h1 h3
  have el : lowS c (glueS c (blockSymbol (rep P)) (blockSymbol (rep T))) = blockSymbol (rep P) := by
    funext k; unfold lowS glueS
    split_ifs with hk
    · rfl
    · exact (trivial_of_zeroFrom h2 hP hPc k (by omega)).symm
  have eh : highS c (glueS c (blockSymbol (rep P)) (blockSymbol (rep T))) = blockSymbol (rep T) := by
    funext k; unfold highS glueS
    split_ifs with hk
    · exact (trivial_of_zeroBelow h2 hT hTc k (by omega)).symm
    · rfl
  rw [el] at h1; rw [eh] at h3
  exact ⟨h1, h3⟩

end Glue

/-! ### Cuts -/

/-- A cut of a profile at $c$: some constituent below $2^c$, and the constituents of scales $2^c$, $2^{c+1}$ are
zero-dimensional. -/
def CutAt (d : ℕ → ℕ) (c : ℕ) : Prop := (∃ k < c, d k ≠ 0) ∧ d c = 0 ∧ d (c + 1) = 0

open Classical in
/-- The first cut of a profile (`0` if there is none). -/
def cutF (d : ℕ → ℕ) : ℕ := if h : ∃ c, CutAt d c then Nat.find h else 0

theorem cutF_spec {d : ℕ → ℕ} (h : ∃ c, CutAt d c) : CutAt d (cutF d) := by
  classical
  unfold cutF; rw [dif_pos h]; exact Nat.find_spec h

theorem cutF_min {d : ℕ → ℕ} {c : ℕ} (h : CutAt d c) : cutF d ≤ c := by
  classical
  have h' : ∃ c, CutAt d c := ⟨c, h⟩
  unfold cutF; rw [dif_pos h']; exact Nat.find_min' h' h

theorem cutF_eq {d : ℕ → ℕ} {c : ℕ} (h : CutAt d c) (hmin : ∀ c' < c, ¬ CutAt d c') : cutF d = c := by
  have h1 := cutF_min h
  by_contra hne
  exact hmin _ (by omega) (cutF_spec ⟨c, h⟩)

/-- Profiles agreeing up to $c+1$ have the same cuts at $c' \le c$. -/
theorem cutAt_congr {d d' : ℕ → ℕ} {c : ℕ} (h : ∀ k ≤ c + 1, d k = d' k) {c' : ℕ} (hc' : c' ≤ c) :
    CutAt d c' ↔ CutAt d' c' := by
  unfold CutAt
  constructor
  · rintro ⟨⟨k, hk, hne⟩, h1, h2⟩
    exact ⟨⟨k, hk, by rwa [← h k (by omega)]⟩, by rwa [← h c' (by omega)], by rwa [← h (c' + 1) (by omega)]⟩
  · rintro ⟨⟨k, hk, hne⟩, h1, h2⟩
    exact ⟨⟨k, hk, by rwa [h k (by omega)]⟩, by rwa [h c' (by omega)], by rwa [h (c' + 1) (by omega)]⟩

theorem cutF_congr {d d' : ℕ → ℕ} (hc : ∃ c, CutAt d c) (h : ∀ k ≤ cutF d + 1, d k = d' k) :
    cutF d' = cutF d := by
  have hs := cutF_spec hc
  refine cutF_eq ((cutAt_congr h le_rfl).1 hs) fun c' hc' hcut => ?_
  have := cutF_min ((cutAt_congr h hc'.le).2 hcut)
  omega

/-- The **cut** of a genus. -/
def cutG {n : ℕ} (G : LocGenus v n) : ℕ := cutF (dG G)

theorem cutG_eq {n : ℕ} (G : LocGenus v n) : cutG G = cutF (dG G) := rfl

/-- $G$ has a gap: a cut with nonzero constituents above it. -/
def Red {n : ℕ} (G : LocGenus v n) : Prop := (∃ c, CutAt (dG G) c) ∧ ∃ k, cutG G < k ∧ dG G k ≠ 0

/-- $P$ is **irreducible**: a cut with nothing above it. -/
def Irred {n : ℕ} (P : LocGenus v n) : Prop := (∃ c, CutAt (dG P) c) ∧ ZeroFrom P (cutG P)

/-- The bottom piece of a genus (as a genus in $p$ variables). -/
def bottom (p : ℕ) {n : ℕ} (G : LocGenus v n) : LocGenus v p := genusOf v p (lowL (cutG G) (rep G))

/-- The top piece of a genus (as a genus in $q$ variables). -/
def top (q : ℕ) {n : ℕ} (G : LocGenus v n) : LocGenus v q := genusOf v q (highL (cutG G) (rep G))

/-- The rank of the bottom piece. -/
def pB {n : ℕ} (G : LocGenus v n) : ℕ := dyDim (lowL (cutG G) (rep G))

section Pieces

variable (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
include h2

theorem dyDim_low_high (D : List DyBlock) (c : ℕ) : dyDim (lowL c D) + dyDim (highL c D) = dyDim D := by
  rw [← dyDim_append, dyDim_eq_sum_dim, dyDim_eq_sum_dim]
  refine List.Perm.sum_eq (List.Perm.map _ ?_)
  have := List.filter_append_perm (fun b => decide (blockExp b ≤ (c : ℤ))) D
  refine List.Perm.trans ?_ this
  unfold lowL highL
  refine List.Perm.append_left _ (List.Perm.of_eq (List.filter_congr fun b _ => ?_))
  by_cases h : blockExp b ≤ (c : ℤ) <;> simp [h] <;> omega

theorem isRep_bottom {n : ℕ} {G : LocGenus v n} (hG : G.Nondeg) :
    IsRep (bottom (pB G) G) (lowL (cutG G) (rep G)) :=
  ⟨(isRep_rep h2 hG).1.lowL, rfl, rfl⟩

theorem isRep_top {n : ℕ} {G : LocGenus v n} (hG : G.Nondeg) :
    IsRep (top (n - pB G) G) (highL (cutG G) (rep G)) := by
  refine ⟨(isRep_rep h2 hG).1.highL, ?_, rfl⟩
  have := dyDim_low_high h2 (rep G) (cutG G)
  rw [(isRep_rep h2 hG).2.1] at this
  unfold pB; omega

theorem dG_bottom {n : ℕ} {G : LocGenus v n} (hG : G.Nondeg) (k : ℕ) :
    dG (bottom (pB G) G) k = if k ≤ cutG G then dG G k else 0 := by
  rw [← (isRep_bottom h2 hG).dim_eq h2, blockSymbol_lowL]
  unfold lowS glueS dG
  split_ifs <;> rfl

theorem dG_top {n : ℕ} {G : LocGenus v n} (hG : G.Nondeg) (k : ℕ) :
    dG (top (n - pB G) G) k = if k ≤ cutG G then 0 else dG G k := by
  rw [← (isRep_top h2 hG).dim_eq h2, blockSymbol_highL]
  unfold highS glueS dG
  split_ifs <;> rfl

theorem pB_le {n : ℕ} {G : LocGenus v n} (hG : G.Nondeg) : pB G ≤ n := by
  have := dyDim_low_high h2 (rep G) (cutG G)
  rw [(isRep_rep h2 hG).2.1] at this
  unfold pB; omega

/-- **A genus with a gap is glued from its bottom and top pieces.** -/
theorem glueN_bottom_top {n : ℕ} {G : LocGenus v n} (hG : G.Nondeg) (hR : Red G) :
    glueN n (bottom (pB G) G) (top (n - pB G) G) = G := by
  have hb := isRep_bottom h2 hG
  have ht := isRep_top h2 hG
  have hcut := cutF_spec hR.1
  set c := cutG G
  have hPc : ZeroFrom (bottom (pB G) G) c := fun k hk => by
    rw [dG_bottom h2 hG]; split_ifs with h
    · have : k = c := by omega
      rw [this]; exact hcut.2.1
    · rfl
  have hTc : ZeroBelow (top (n - pB G) G) (c + 2) := fun k hk => by
    rw [dG_top h2 hG]; split_ifs with h
    · rfl
    · have : k = c + 1 := by omega
      rw [this]; exact hcut.2.2
  have g := isRep_glueN h2 hb.nondeg ht.nondeg (show pB G + (n - pB G) = n by have := pB_le h2 hG; omega)
  have hG' := isRep_rep h2 hG
  refine (g.2.2.symm.trans ?_).trans hG'.2.2
  refine (genusOf_eq_iff' h2 g.1 hG'.1 g.2.1 hG'.2.1).2 ?_
  rw [blockSymbol_glue h2 hb.nondeg ht.nondeg hPc hTc, ← lowL_append_highL c (rep G),
    blockSymbol_append (c := c) (fun b hb => (mem_lowL.1 hb).2) (fun b hb => (mem_highL.1 hb).2)]
  refine moveEquiv_glue (hb.moveEquiv h2 (isRep_rep h2 hb.nondeg)).symm
    (ht.moveEquiv h2 (isRep_rep h2 ht.nondeg)).symm ?_ ?_
  · intro k hk hI
    rw [isTypeI_blockSymbol_iff] at hI
    obtain ⟨x, hx, hxk, -⟩ := hI
    have := exps_low h2 (isRep_rep h2 hb.nondeg) hPc x hx
    rw [hxk] at this
    have hkc : k = c := by exact_mod_cast le_antisymm this (by exact_mod_cast hk)
    have := (dim_blockSymbol_ne_zero_iff _ k).2 ⟨x, hx, hxk⟩
    rw [(isRep_rep h2 hb.nondeg).dim_eq h2, hkc] at this
    exact this (hPc c le_rfl)
  · intro k hk hI
    rw [isTypeI_blockSymbol_iff] at hI
    obtain ⟨x, hx, hxk, -⟩ := hI
    have := exps_high h2 (isRep_rep h2 ht.nondeg) hTc x hx
    rw [hxk] at this
    have : c < k := by exact_mod_cast this
    have h3 := (dim_blockSymbol_ne_zero_iff _ k).2 ⟨x, hx, hxk⟩
    rw [(isRep_rep h2 ht.nondeg).dim_eq h2] at h3
    exact h3 (hTc k (by omega))

/-- The cut of a glued genus is the cut of its bottom piece, if that piece is irreducible. -/
theorem cutG_glueN {n p q : ℕ} {P : LocGenus v p} {T : LocGenus v q} (hP : P.Nondeg) (hT : T.Nondeg)
    (hn : p + q = n) (hI : Irred P) (hTc : ZeroBelow T (cutG P + 2)) : cutG (glueN n P T) = cutG P := by
  unfold cutG
  refine cutF_congr hI.1 fun k hk => ?_
  rw [dG_glueN h2 hP hT hn hI.2 hTc, hTc k (by have : cutG P = cutF (dG P) := rfl; omega), add_zero]

theorem bottom_glueN {n p q : ℕ} {P : LocGenus v p} {T : LocGenus v q} (hP : P.Nondeg) (hT : T.Nondeg)
    (hn : p + q = n) (hI : Irred P) (hTc : ZeroBelow T (cutG P + 2)) :
    pB (glueN n P T) = p ∧ bottom p (glueN n P T) = P := by
  have hc := cutG_glueN h2 hP hT hn hI hTc
  obtain ⟨h1, -⟩ := moveEquiv_low_glue h2 hP hT hn hI.2 hTc
  have g := isRep_rep h2 (isRep_glueN h2 hP hT hn).nondeg
  have a := isRep_rep h2 hP
  have gl : AdmL (lowL (cutG P) (rep (glueN n P T))) := g.1.lowL
  have e : pB (glueN n P T) = dyDim (lowL (cutG P) (rep (glueN n P T))) := by
    unfold pB; rw [hc]
  have hd : dyDim (lowL (cutG P) (rep (glueN n P T))) = p := by
    rw [dyDim_eq_of_moveEquiv gl a.1 h1, a.2.1]
  refine ⟨e.trans hd, ?_⟩
  have hb : bottom p (glueN n P T) = genusOf v p (lowL (cutG P) (rep (glueN n P T))) := by
    unfold bottom; rw [hc]
  rw [hb]
  refine Eq.trans ?_ a.2.2
  exact (genusOf_eq_iff' h2 gl a.1 hd a.2.1).2 h1

theorem top_glueN {n p q : ℕ} {P : LocGenus v p} {T : LocGenus v q} (hP : P.Nondeg) (hT : T.Nondeg)
    (hn : p + q = n) (hI : Irred P) (hTc : ZeroBelow T (cutG P + 2)) : top q (glueN n P T) = T := by
  have hc := cutG_glueN h2 hP hT hn hI hTc
  obtain ⟨-, h1⟩ := moveEquiv_low_glue h2 hP hT hn hI.2 hTc
  have g := isRep_rep h2 (isRep_glueN h2 hP hT hn).nondeg
  have b := isRep_rep h2 hT
  have gh : AdmL (highL (cutG P) (rep (glueN n P T))) := g.1.highL
  have hd : dyDim (highL (cutG P) (rep (glueN n P T))) = q := by
    rw [dyDim_eq_of_moveEquiv gh b.1 h1, b.2.1]
  have hb : top q (glueN n P T) = genusOf v q (highL (cutG P) (rep (glueN n P T))) := by
    unfold top; rw [hc]
  rw [hb]
  refine Eq.trans ?_ b.2.2
  exact (genusOf_eq_iff' h2 gh b.1 hd b.2.1).2 h1

theorem red_glueN {n p q : ℕ} {P : LocGenus v p} {T : LocGenus v q} (hP : P.Nondeg) (hT : T.Nondeg)
    (hn : p + q = n) (hI : Irred P) (hTc : ZeroBelow T (cutG P + 2)) (hq : 1 ≤ q) : Red (glueN n P T) := by
  have hc := cutG_glueN h2 hP hT hn hI hTc
  have b := isRep_rep h2 hT
  obtain ⟨x, hx⟩ : ∃ x, x ∈ rep T := by
    rcases hrep : rep T with _ | ⟨x, l⟩
    · have := b.2.1; rw [hrep] at this; simp [dyDim] at this; omega
    · exact ⟨x, by simp⟩
  obtain ⟨k, -, hk⟩ := b.exp_mem h2 hx
  have hkc : cutG P + 2 ≤ k := by
    by_contra h; exact hk (hTc k (by omega))
  refine ⟨⟨cutG P, ?_⟩, k, by omega, ?_⟩
  · have := cutF_spec hI.1
    have hc' : cutG P = cutF (dG (glueN n P T)) := hc.symm
    rw [hc']; exact cutF_spec ⟨cutG P, (cutAt_congr (d := dG P) (d' := dG (glueN n P T)) (c := cutG P)
      (fun j hj => by rw [dG_glueN h2 hP hT hn hI.2 hTc, hTc j (by omega), add_zero]) le_rfl).1 this⟩
  · rw [dG_glueN h2 hP hT hn hI.2 hTc]; omega

theorem irred_bottom {n : ℕ} {G : LocGenus v n} (hG : G.Nondeg) (hR : Red G) : Irred (bottom (pB G) G) := by
  have hcut := cutF_spec hR.1
  have e : ∀ k ≤ cutG G + 1, dG G k = dG (bottom (pB G) G) k := fun k hk => by
    rw [dG_bottom h2 hG]; split_ifs with h
    · rfl
    · have : k = cutG G + 1 := by omega
      rw [this]; exact hcut.2.2
  have hc : cutG (bottom (pB G) G) = cutG G := cutF_congr hR.1 e
  refine ⟨⟨cutG G, (cutAt_congr e le_rfl).1 hcut⟩, fun k hk => ?_⟩
  rw [hc] at hk
  rw [dG_bottom h2 hG]; split_ifs with h
  · have : k = cutG G := by omega
    rw [this]; exact hcut.2.1
  · rfl

theorem cutG_bottom {n : ℕ} {G : LocGenus v n} (hG : G.Nondeg) (hR : Red G) :
    cutG (bottom (pB G) G) = cutG G := by
  have hcut := cutF_spec hR.1
  refine cutF_congr hR.1 fun k hk => ?_
  rw [dG_bottom h2 hG]; split_ifs with h
  · rfl
  · have : k = cutG G + 1 := by have := cutG_eq G; omega
    rw [this]; exact hcut.2.2

theorem zeroBelow_top {n : ℕ} {G : LocGenus v n} (hG : G.Nondeg) (hR : Red G) :
    ZeroBelow (top (n - pB G) G) (cutG G + 2) := fun k hk => by
  have hcut := cutF_spec hR.1
  rw [dG_top h2 hG]; split_ifs with h
  · rfl
  · have : k = cutG G + 1 := by omega
    rw [this]; exact hcut.2.2

theorem pB_pos {n : ℕ} {G : LocGenus v n} (hG : G.Nondeg) (hR : Red G) : 1 ≤ pB G ∧ pB G < n := by
  have hcut := cutF_spec hR.1
  have hb := isRep_bottom h2 hG
  have ht := isRep_top h2 hG
  have hle := pB_le h2 hG
  obtain ⟨k, hk, hne⟩ := hcut.1
  obtain ⟨k', hk', hne'⟩ := hR.2
  have h1 : (blockSymbol (lowL (cutG G) (rep G)) k).dim ≠ 0 := by
    rw [hb.dim_eq h2, dG_bottom h2 hG, if_pos (by have := cutG_eq G; omega)]; exact hne
  have h3 : (blockSymbol (highL (cutG G) (rep G)) k').dim ≠ 0 := by
    rw [ht.dim_eq h2, dG_top h2 hG, if_neg (by omega)]; exact hne'
  obtain ⟨x, hx, -⟩ := (dim_blockSymbol_ne_zero_iff _ k).1 h1
  obtain ⟨y, hy, -⟩ := (dim_blockSymbol_ne_zero_iff _ k').1 h3
  have p1 : 1 ≤ dyDim (lowL (cutG G) (rep G)) := by
    rw [dyDim_eq_sum_dim]
    have := List.le_sum_of_mem (List.mem_map_of_mem (f := DyBlock.dim) hx)
    have : 1 ≤ x.dim := by cases x <;> simp [DyBlock.dim]
    omega
  have p2 : 1 ≤ dyDim (highL (cutG G) (rep G)) := by
    rw [dyDim_eq_sum_dim]
    have := List.le_sum_of_mem (List.mem_map_of_mem (f := DyBlock.dim) hy)
    have : 1 ≤ y.dim := by cases y <;> simp [DyBlock.dim]
    omega
  have := ht.2.1
  have e : pB G = dyDim (lowL (cutG G) (rep G)) := rfl
  omega

end Pieces

/-! ### The double shift -/

section Shift

variable (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
include h2

theorem h0_shiftL {D : List DyBlock} (h0 : ∀ b ∈ D, 0 ≤ blockExp b) : ∀ b ∈ shiftL D, 0 ≤ blockExp b := by
  intro b hb
  obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
  rw [blockExp_shift1]; have := h0 b' hb'; omega

theorem isRep_Sh2 {q : ℕ} {T : LocGenus v q} (hT : T.Nondeg) : IsRep (Sh2 T) (shiftL (shiftL (rep T))) := by
  have b := isRep_rep h2 hT
  exact ⟨b.1.shiftL.shiftL, by rw [dyDim_shiftL, dyDim_shiftL, b.2.1], rfl⟩

theorem blockSymbol_Sh2 {q : ℕ} {T : LocGenus v q} (hT : T.Nondeg) :
    blockSymbol (shiftL (shiftL (rep T))) = shS (shS (blockSymbol (rep T))) := by
  have b := isRep_rep h2 hT
  rw [blockSymbol_shiftL (h0_shiftL h2 b.1.2.1), blockSymbol_shiftL b.1.2.1]

theorem dG_Sh2 {q : ℕ} {T : LocGenus v q} (hT : T.Nondeg) (k : ℕ) :
    dG (Sh2 T) k = if k < 2 then 0 else dG T (k - 2) := by
  rw [← (isRep_Sh2 h2 hT).dim_eq h2, blockSymbol_Sh2 h2 hT]
  rcases k with _ | _ | k
  · rfl
  · rfl
  · simp [dG]

theorem st_Sh2 {q : ℕ} {T : LocGenus v q} (hT : T.Nondeg) : st (Sh2 T) = st T := by
  have b := isRep_rep h2 hT
  rw [(isRep_Sh2 h2 hT).st_eq h2, b.st_eq h2, valSum_shiftL (h0_shiftL h2 b.1.2.1), valSum_shiftL b.1.2.1,
    dyDim_shiftL, unitProd_shiftL, unitProd_shiftL, hasseQ_shiftL_two b.1.2.1]
  congr 1
  push_cast
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem νG_Sh2 {q : ℕ} {T : LocGenus v q} (hT : T.Nondeg) : νG (Sh2 T) = νG T + 2 * q := by
  have b := isRep_rep h2 hT
  rw [← (isRep_Sh2 h2 hT).valSum_eq h2, valSum_shiftL (h0_shiftL h2 b.1.2.1), valSum_shiftL b.1.2.1,
    dyDim_shiftL, b.2.1]
  unfold νG; ring

theorem invBeta_Sh2 {q : ℕ} {T : LocGenus v q} (hT : T.Nondeg) :
    ((Sh2 T).beta)⁻¹ * 2 ^ (q * (q + 1)) = (T.beta)⁻¹ := by
  have b := isRep_rep h2 hT
  have s := isRep_Sh2 h2 hT
  obtain ⟨N, hN⟩ := blockSymbol_supported (rep T) b.1.2.1
  have hN2 : (blockSymbol (shiftL (shiftL (rep T)))).SupportedBelow (N + 2) := by
    rw [blockSymbol_Sh2 h2 hT]
    intro k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
    exact hN k' (by omega)
  rw [show Sh2 T = genusOf v q (shiftL (shiftL (rep T))) from rfl, invBeta_genusOf h2 s.1 s.2.1 hN2]
  conv_rhs => rw [← b.2.2, invBeta_genusOf h2 b.1 b.2.1 hN]
  rw [blockSymbol_Sh2 h2 hT, pMassTwo_shS, pMassTwo_shS, valSum_shiftL (h0_shiftL h2 b.1.2.1),
    valSum_shiftL b.1.2.1, dyDim_shiftL, b.2.1]
  have hs : ∀ m : ℕ, Real.sqrt 2 ^ m ≠ 0 := fun m => pow_ne_zero _ (by positivity)
  rw [← sqrt_two_pow_mul]
  field_simp
  rw [mul_assoc, ← pow_add]
  congr 2; ring

theorem Sh2_injective {q : ℕ} {T T' : LocGenus v q} (hT : T.Nondeg) (hT' : T'.Nondeg) (h : Sh2 T = Sh2 T') :
    T = T' := by
  have b := isRep_rep h2 hT
  have b' := isRep_rep h2 hT'
  have hme := (isRep_Sh2 h2 hT).moveEquiv h2 (h ▸ isRep_Sh2 h2 hT')
  rw [blockSymbol_Sh2 h2 hT, blockSymbol_Sh2 h2 hT'] at hme
  obtain ⟨N, hN⟩ := blockSymbol_supported (rep T) b.1.2.1
  have hB : ∀ k, N ≤ k → ¬ IsTypeI (blockSymbol (rep T)) k := fun k hk => by
    unfold IsTypeI; rw [hN k hk]; exact not_isTypeI_trivial
  have hB1 : ∀ k, N + 1 ≤ k → ¬ IsTypeI (shS (blockSymbol (rep T))) k := fun k hk => by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    exact hB k' (by omega)
  have h1 := moveEquiv_of_shS hB (moveEquiv_of_shS hB1 hme)
  rw [← b.2.2, ← b'.2.2]
  exact (genusOf_eq_iff' h2 b.1 b'.1 b.2.1 b'.2.1).2 h1

/-- Every genus vanishing below $2^{m+2}$ is a double shift of a genus vanishing below $2^m$, provided $m \ge 1$.
(*Correction of the draft statement:* for $m = 0$ it is false, since a rank one block $2^2u\,x^2$ of $H$ would be the shift
of the non-admissible block $2^0u$, i.e. $Q = \tfrac12 u x^2$.) -/
theorem exists_Sh2 {q : ℕ} {G : LocGenus v q} (hG : G.Nondeg) {m : ℕ} (hm : 1 ≤ m) (hz : ZeroBelow G (m + 2)) :
    ∃ T : LocGenus v q, T.Nondeg ∧ ZeroBelow T m ∧ Sh2 T = G := by
  have a := isRep_rep h2 hG
  -- lower every exponent by two
  let down : DyBlock → DyBlock := fun b => match b with
    | .sq e u => .sq (e - 2) u
    | .hyp e => .hyp (e - 2)
    | .ell e => .ell (e - 2)
  have hge : ∀ b ∈ rep G, (m : ℤ) + 2 ≤ blockExp b := by
    intro b hb
    obtain ⟨k, hk, hne⟩ := a.exp_mem h2 hb
    rw [hk]; by_contra h; exact hne (hz k (by push_cast at h; omega))
  set B := (rep G).map down with hBdef
  have hsd : ∀ b ∈ rep G, shift1 (shift1 (down b)) = b := by
    intro b hb
    cases b <;> simp [down, shift1] <;> ring
  have hBshift : shiftL (shiftL B) = rep G := by
    unfold shiftL; rw [hBdef, List.map_map, List.map_map]
    conv_rhs => rw [← List.map_id (rep G)]
    exact List.map_congr_left fun b hb => hsd b hb
  have hBA : AdmL B := by
    refine ⟨fun b hb => ?_, fun b hb => ?_, fun b hb => ?_⟩ <;> obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
    · have := a.1.1 b' hb'; cases b' <;> exact this
    · have := hge b' hb'; cases b' <;> simp [down, blockExp] at this ⊢ <;> omega
    · have := hge b' hb'; cases b' <;> simp [down, blockExp, IsOddUnimodBlock] at this ⊢ <;> omega
  have hBn : dyDim B = q := by rw [← dyDim_shiftL, ← dyDim_shiftL, hBshift, a.2.1]
  set T := genusOf v q B
  have hTr : IsRep T B := ⟨hBA, hBn, rfl⟩
  refine ⟨T, hTr.nondeg, fun k hk => ?_, ?_⟩
  · rw [← hTr.dim_eq h2]
    have : blockSymbol (shiftL (shiftL B)) (k + 2) = blockSymbol B k := by
      rw [blockSymbol_shiftL (h0_shiftL h2 hBA.2.1), blockSymbol_shiftL hBA.2.1]; rfl
    rw [← this, hBshift]; exact hz _ (by omega)
  · have s := isRep_Sh2 h2 hTr.nondeg
    refine (s.2.2.symm.trans ?_).trans a.2.2
    refine (genusOf_eq_iff' h2 s.1 a.1 s.2.1 a.2.1).2 ?_
    rw [blockSymbol_Sh2 h2 hTr.nondeg, ← hBshift, blockSymbol_shiftL (h0_shiftL h2 hBA.2.1),
      blockSymbol_shiftL hBA.2.1]
    exact moveEquiv_shS (moveEquiv_shS (hTr.moveEquiv h2 (isRep_rep h2 hTr.nondeg)).symm)

end Shift

end

end QuadFormsKB.Hanke2011Structure.RatTwo
