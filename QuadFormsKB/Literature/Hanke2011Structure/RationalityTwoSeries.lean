/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Literature.Hanke2011Structure.RationalityTwoGenus
import QuadFormsKB.Literature.Hanke2011Structure.RationalityOddGenus

/-!
# Paper 6, Theorem 5.4 and Corollary 5.5 at $p = 2$, every rank $n$, over $\mathbb Q$

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (`hanke2011structure`), Thm. 5.4, pp. 23–24, and Cor. 5.5, p. 24.

For $v$ the prime of $\mathbb Q$ above $2$, every rank $n$, every odd integer $w$ and every reference genus $G_0$,
the fixed-unit local series
$$\sum_\nu A^*_{2;n}([2^\nu w])\,X^\nu,\qquad \sum_\nu B^*_{2;n}([2^\nu w])\,X^\nu\qquad(X = 2^{-s})$$
of the **true** local genera (`trueAstar2`, `trueBstar2`: sums over the nondegenerate primitive $\mathbb Z_2$-genera $G$
with $\det_H G = [2^\nu w]$ of $\beta(G_0)/\beta(G)$, without / with the Hasse invariant $c_2(G)$ as a sign) are
rational functions of $X$ (`theorem_5_4_two_A_rank`, `theorem_5_4_two_B_rank`; `RatOdd.RatSeries`: $S\,Q = P$ with
$Q(0) \ne 0$), and so are the Euler factors of Cor. 5.5 for $\lambda(2^i) = 2^i$ (`cor_5_5_two_A_rank`,
`cor_5_5_two_B_rank`).  Unconditional.

*Proof* (the paper's argument, p. 24, made precise).  Write a genus through a block decomposition (Conway–Sloane
2-adic symbols, Theorem 10).  The *bottom piece* of $G$ consists of the Jordan constituents below the first pair of
adjacent zero-dimensional constituents (`cutG`); if anything lies above, $G = P \perp T$ glued from its bottom piece
$P$ and its top piece $T$ (`glueN_bottom_top`), and the pair $(P, T)$ is determined by $G$ (`bottom_glueN`,
`top_glueN`).  Across the gap no move (sign walking, oddity fusion) is possible, the state $(\nu \bmod 2, u, c_2)$
of $P \perp T$ is a function of the states of $P$ and $T$, and the inverse density is
$\beta(P)^{-1}\beta(T)^{-1}2^{pq-1-\nu_Pq}$: the scale of $T$ enters only through the cross product of Conway–Sloane's
mass formula.  For a fixed irreducible bottom piece $P$ (finitely many, since its scales are bounded,
`irred_zeroFrom`) the sum over $T$ is the series of the genera of rank $q$ vanishing below the scale $2^{c+2}$; raising
all scales of $T$ by two (`Sh2`) is a bijection onto those vanishing below $2^{c+4}$ which keeps the state and divides
the inverse density by $2^{q(q+1)}$, so that series times $1 - 2^{-q(q+1)}X^{2q}$ is the sum of two series of the same
kind with lower rank (`serU_mul`).  Strong induction on the rank (`ratE`, `ratQ`) gives rationality.

Indices are 0-based.
-/

open IsDedekindDomain NumberField Finset PowerSeries

namespace QuadFormsKB.Hanke2011Structure.RatTwo

open QuadFormsKB.ConwaySloane QuadFormsKB.ConwaySloane.Mass QuadFormsKB.Dyadic7 Cassels
  QuadFormsKB.Hanke2011Structure
open QuadFormsKB.Hanke2011Structure.RatOdd (RatSeries)

noncomputable section

variable {v : HeightOneSpectrum (𝓞 ℚ)}

/-! ### Weighted generating series of sets of genera -/

/-- The coefficient $\sum_{G \in S_\nu}\psi(\mathrm{st}\,G)\,\beta(G)^{-1}$. -/
def coefS {r : ℕ} (S : ℕ → Set (LocGenus v r)) (ψ : State → ℝ) (ν : ℕ) : ℝ :=
  ∑ᶠ G ∈ S ν, ψ (st G) * (G.beta)⁻¹

/-- The series $\sum_\nu \mathrm{coefS}\,X^\nu$. -/
def serS {r : ℕ} (S : ℕ → Set (LocGenus v r)) (ψ : State → ℝ) : PowerSeries ℝ := PowerSeries.mk (coefS S ψ)

/-- The genera whose symbol satisfies $Q$, with $\nu(G) = \nu$. -/
def Qset (v : HeightOneSpectrum (𝓞 ℚ)) (r : ℕ) (Q : TwoSymbol → Prop) (ν : ℕ) : Set (LocGenus v r) :=
  {G | G.Nondeg ∧ Q (blockSymbol (rep G)) ∧ νG G = ν}

/-- The genera vanishing below the scale $2^m$, with $\nu(G) = \nu$. -/
def Uset (v : HeightOneSpectrum (𝓞 ℚ)) (r m : ℕ) (ν : ℕ) : Set (LocGenus v r) :=
  {G | G.Nondeg ∧ ZeroBelow G m ∧ νG G = ν}

/-- The symbol has lowest scale exactly $2^m$. -/
def QE (m : ℕ) (σ : TwoSymbol) : Prop := (∀ k < m, (σ k).dim = 0) ∧ (σ m).dim ≠ 0

/-! ### Finiteness -/

section Fin

variable (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
include h2

theorem finite_bound (r B : ℕ) :
    {G : LocGenus v r | G.Nondeg ∧ ∀ k, B ≤ k → dG G k = 0}.Finite := by
  classical
  refine ((finite_lists (alphabet B) r).image (fun D => genusOf v r D)).subset ?_
  rintro G ⟨hN, hB⟩
  have a := isRep_rep h2 hN
  refine ⟨rep G, ⟨le_of_le_of_eq (length_le_dyDim _) a.2.1, fun b hb => ?_⟩, a.2.2⟩
  obtain ⟨k, hk, hne⟩ := a.exp_mem h2 hb
  refine mem_alphabet (a.1.1 b hb) (a.1.2.1 b hb) ?_
  rw [hk, Int.toNat_natCast]
  by_contra h
  exact hne (hB k (by omega))

theorem finite_nu (r ν : ℕ) : {G : LocGenus v r | G.Nondeg ∧ νG G = ν}.Finite := by
  refine (finite_bound h2 r (ν + 1)).subset ?_
  rintro G ⟨hN, hν⟩
  refine ⟨hN, fun k hk => ?_⟩
  by_contra hne
  have a := isRep_rep h2 hN
  rw [← a.dim_eq h2] at hne
  obtain ⟨b, hb, hbk⟩ := (dim_blockSymbol_ne_zero_iff _ k).1 hne
  have := exp_le_valSum hb
  rw [hbk, Int.toNat_natCast, a.valSum_eq h2, hν] at this
  omega

theorem finite_sub {r : ℕ} (S : Set (LocGenus v r)) (ν : ℕ) (hS : ∀ G ∈ S, G.Nondeg ∧ νG G = ν) : S.Finite :=
  (finite_nu h2 r ν).subset hS

/-- The rank is the sum of the profile. -/
theorem rank_eq_sum {r : ℕ} {G : LocGenus v r} (hN : G.Nondeg) :
    ∃ N₀, ∀ N, N₀ ≤ N → r = ∑ k ∈ range N, dG G k := by
  have a := isRep_rep h2 hN
  obtain ⟨N₀, hN₀⟩ := blockSymbol_supported (rep G) a.1.2.1
  refine ⟨N₀, fun N hN => ?_⟩
  have hb : ∀ b ∈ rep G, blockExp b < N := by
    intro b hb
    obtain ⟨k, hk, hne⟩ := a.exp_mem h2 hb
    rw [hk]; by_contra h
    exact hne (by rw [show dG G k = (blockSymbol (rep G) k).dim from rfl, hN₀ k (by push_cast at h; omega)]; rfl)
  exact a.2.1.symm.trans (dyDim_eq_sum a.1.2.1 hb)

theorem support_finite {r : ℕ} {G : LocGenus v r} (hN : G.Nondeg) : ∃ N, ∀ k, N ≤ k → dG G k = 0 := by
  have a := isRep_rep h2 hN
  obtain ⟨N₀, hN₀⟩ := blockSymbol_supported (rep G) a.1.2.1
  exact ⟨N₀, fun k hk => by rw [show dG G k = (blockSymbol (rep G) k).dim from rfl, hN₀ k hk]; rfl⟩

end Fin

theorem sum_pairs (d : ℕ → ℕ) (k₀ : ℕ) :
    ∀ t : ℕ, (∀ j, k₀ ≤ j → j + 1 < k₀ + 2 * t → d j ≠ 0 ∨ d (j + 1) ≠ 0) →
      t ≤ ∑ j ∈ Ico k₀ (k₀ + 2 * t), d j := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro h
    have h1 := ih fun j hj1 hj2 => h j hj1 (by omega)
    rw [show k₀ + 2 * (t + 1) = (k₀ + 2 * t) + 1 + 1 by ring, Finset.sum_Ico_succ_top (by omega),
      Finset.sum_Ico_succ_top (by omega)]
    have := h (k₀ + 2 * t) (by omega) (by omega)
    omega

theorem irred_zeroFrom (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {p : ℕ} {P : LocGenus v p} (hN : P.Nondeg) (hI : Irred P)
    {M : ℕ} (hM : ∃ k ≤ M, dG P k ≠ 0) : ZeroFrom P (M + 2 * p + 2) := by
  obtain ⟨k₀, hk₀, hne⟩ := hM
  have hcut := cutF_spec hI.1
  have hc : cutG P < k₀ + 2 * p + 2 := by
    by_contra hcon
    have hpairs : ∀ j, k₀ ≤ j → j + 1 < k₀ + 2 * (p + 1) → dG P j ≠ 0 ∨ dG P (j + 1) ≠ 0 := by
      intro j hj1 hj2
      by_contra hz
      push_neg at hz
      have hj : j < cutG P := by omega
      have hcut' : CutAt (dG P) j := by
        refine ⟨⟨k₀, ?_, hne⟩, hz.1, hz.2⟩
        rcases Nat.eq_or_lt_of_le hj1 with h | h
        · exact absurd (h ▸ hz.1) hne
        · exact h
      have := cutF_min hcut'
      unfold cutG at hj; omega
    have h1 := sum_pairs (dG P) k₀ (p + 1) hpairs
    obtain ⟨N₀, hN₀⟩ := rank_eq_sum h2 hN
    have h2' := hN₀ (max N₀ (k₀ + 2 * (p + 1))) (le_max_left _ _)
    have h3 : ∑ j ∈ Ico k₀ (k₀ + 2 * (p + 1)), dG P j ≤ ∑ j ∈ range (max N₀ (k₀ + 2 * (p + 1))), dG P j := by
      rw [Finset.range_eq_Ico]
      exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico (Nat.zero_le _) (le_max_right _ _))
    omega
  intro k hk
  exact hI.2 k (by unfold cutG at hc ⊢; omega)

/-! ### The series of genera vanishing below a scale -/

section U

variable (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
include h2

theorem Uset_eq {r : ℕ} (m : ℕ) (hm : 1 ≤ m) (ν : ℕ) :
    Uset v r m ν = Qset v r (QE m) ν ∪ Qset v r (QE (m + 1)) ν ∪
      Sh2 '' {T | T.Nondeg ∧ ZeroBelow T m ∧ νG T + 2 * r = ν} := by
  ext G
  constructor
  · rintro ⟨hN, hz, hν⟩
    by_cases h0 : dG G m ≠ 0
    · exact Or.inl (Or.inl ⟨hN, ⟨hz, h0⟩, hν⟩)
    · push_neg at h0
      by_cases h1 : dG G (m + 1) ≠ 0
      · refine Or.inl (Or.inr ⟨hN, ⟨fun k hk => ?_, h1⟩, hν⟩)
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
        · exact hz k hk
        · exact h0
      · push_neg at h1
        have hz2 : ZeroBelow G (m + 2) := fun k hk => by
          rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
          · rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
            · exact hz k hk
            · exact h0
          · exact h1
        obtain ⟨T, hT, hTz, rfl⟩ := exists_Sh2 h2 hN hm hz2
        exact Or.inr ⟨T, ⟨hT, hTz, by rw [← νG_Sh2 h2 hT]; exact hν⟩, rfl⟩
  · rintro ((⟨hN, ⟨hz, -⟩, hν⟩ | ⟨hN, ⟨hz, -⟩, hν⟩) | ⟨T, ⟨hT, hTz, hν⟩, rfl⟩)
    · exact ⟨hN, hz, hν⟩
    · exact ⟨hN, fun k hk => hz k (by omega), hν⟩
    · refine ⟨(isRep_Sh2 h2 hT).nondeg, fun k hk => ?_, by rw [νG_Sh2 h2 hT]; exact hν⟩
      rw [dG_Sh2 h2 hT]
      split_ifs with h
      · rfl
      · exact hTz _ (by omega)

/-- **The double-shift recursion**: $U_m\,(1 - 2^{-r(r+1)}X^{2r}) = E_m + E_{m+1}$. -/
theorem serU_mul {r : ℕ} (m : ℕ) (hm : 1 ≤ m) (ψ : State → ℝ) :
    serS (Uset v r m) ψ = serS (Qset v r (QE m)) ψ + serS (Qset v r (QE (m + 1))) ψ +
      PowerSeries.C ((2 : ℝ) ^ (r * (r + 1)))⁻¹ * PowerSeries.X ^ (2 * r) * serS (Uset v r m) ψ := by
  ext ν
  simp only [serS, map_add, PowerSeries.coeff_mk]
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk]
  unfold coefS
  rw [Uset_eq h2 m hm]
  have hfin : ∀ (S : Set (LocGenus v r)), S ⊆ Uset v r m ν → S.Finite := fun S hS =>
    finite_sub h2 S ν fun G hG => ⟨(hS hG).1, (hS hG).2.2⟩
  have d12 : Disjoint (Qset v r (QE m) ν) (Qset v r (QE (m + 1)) ν) := by
    refine Set.disjoint_left.2 fun G h1 h2' => ?_
    exact h1.2.1.2 (h2'.2.1.1 m (by omega))
  have hT : ∀ T ∈ {T : LocGenus v r | T.Nondeg ∧ ZeroBelow T m ∧ νG T + 2 * r = ν}, (Sh2 T).Nondeg ∧
      ZeroBelow (Sh2 T) (m + 2) := fun T hT => ⟨(isRep_Sh2 h2 hT.1).nondeg, fun k hk => by
        rw [dG_Sh2 h2 hT.1]; split_ifs with h
        · rfl
        · exact hT.2.1 _ (by omega)⟩
  have d3 : Disjoint (Qset v r (QE m) ν ∪ Qset v r (QE (m + 1)) ν)
      (Sh2 '' {T | T.Nondeg ∧ ZeroBelow T m ∧ νG T + 2 * r = ν}) := by
    refine Set.disjoint_left.2 fun G h1 h3 => ?_
    obtain ⟨T, hTm, rfl⟩ := h3
    have hz := (hT T hTm).2
    rcases h1 with h1 | h1
    · exact h1.2.1.2 (hz m (by omega))
    · exact h1.2.1.2 (hz (m + 1) (by omega))
  have hsub := (Uset_eq h2 (r := r) m hm ν).symm
  have f1 : (Qset v r (QE m) ν).Finite := hfin _ (fun G hG => by rw [← hsub]; exact Or.inl (Or.inl hG))
  have f2 : (Qset v r (QE (m + 1)) ν).Finite := hfin _ (fun G hG => by rw [← hsub]; exact Or.inl (Or.inr hG))
  have f3 : (Sh2 '' {T : LocGenus v r | T.Nondeg ∧ ZeroBelow T m ∧ νG T + 2 * r = ν}).Finite :=
    hfin _ (fun G hG => by rw [← hsub]; exact Or.inr hG)
  rw [finsum_mem_union d3 (f1.union f2) f3, finsum_mem_union d12 f1 f2]
  congr 1
  rw [finsum_mem_image (fun T hT T' hT' h => Sh2_injective h2 hT.1 hT'.1 h)]
  have step : ∀ T ∈ {T : LocGenus v r | T.Nondeg ∧ ZeroBelow T m ∧ νG T + 2 * r = ν},
      ψ (st (Sh2 T)) * ((Sh2 T).beta)⁻¹ = ((2 : ℝ) ^ (r * (r + 1)))⁻¹ * (ψ (st T) * (T.beta)⁻¹) := by
    intro T hT
    rw [st_Sh2 h2 hT.1, ← invBeta_Sh2 h2 hT.1]
    have : (2 : ℝ) ^ (r * (r + 1)) ≠ 0 := by positivity
    field_simp
  rw [finsum_mem_congr rfl step, ← mul_finsum_mem]
  split_ifs with hν
  · congr 1
    refine finsum_mem_congr ?_ fun _ _ => rfl
    ext T
    simp only [Set.mem_setOf_eq, Uset]
    constructor
    · rintro ⟨a, b, c⟩; exact ⟨a, b, by omega⟩
    · rintro ⟨a, b, c⟩; exact ⟨a, b, by omega⟩
  · rw [show {T : LocGenus v r | T.Nondeg ∧ ZeroBelow T m ∧ νG T + 2 * r = ν} = ∅ by
      ext T; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]; omega]
    simp

theorem ratU_of {r : ℕ} (hr : 1 ≤ r) (m : ℕ) (hm : 1 ≤ m) (ψ : State → ℝ)
    (hE : ∀ m, RatSeries (serS (Qset v r (QE m)) ψ)) : RatSeries (serS (Uset v r m) ψ) := by
  set W : Polynomial ℝ := 1 - Polynomial.C ((2 : ℝ) ^ (r * (r + 1)))⁻¹ * Polynomial.X ^ (2 * r)
  have hW : W.coeff 0 ≠ 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simp [W, show 2 * r ≠ 0 by omega]
  refine RatSeries.of_mul W hW ?_ ((hE m).add (hE (m + 1)))
  have h := serU_mul h2 (r := r) m hm ψ
  simp only [W, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C,
    Polynomial.coe_pow, Polynomial.coe_X]
  linear_combination h

end U

/-! ### The decomposition by bottom pieces -/

/-- The irreducible bottom pieces of rank $p$ whose symbol satisfies $Q$. -/
def IrrSet (v : HeightOneSpectrum (𝓞 ℚ)) (p : ℕ) (Q : TwoSymbol → Prop) : Set (LocGenus v p) :=
  {P | P.Nondeg ∧ Irred P ∧ Q (blockSymbol (rep P))}

/-- The state map of gluing with a fixed bottom piece $P$ of rank $p$ to a top piece of rank $q$. -/
def gam {p : ℕ} (P : LocGenus v p) (q : ℕ) (s : State) : State :=
  ((νG P : ZMod 2) + s.1, uG P * s.2.1, P.hasse * s.2.2 * crossSign (νG P) p (uG P) s.1.val q s.2.1)

/-- The constant of gluing with a fixed bottom piece $P$: $\beta(P)^{-1}2^{pq}/(2\cdot2^{\nu_Pq})$. -/
def kap {p : ℕ} (P : LocGenus v p) (q : ℕ) : ℝ := (P.beta)⁻¹ * 2 ^ (p * q) / (2 * 2 ^ (νG P * q))

theorem crossSign_mod (a n : ℕ) (u : ZMod 8) (b m : ℕ) (w : ZMod 8) :
    crossSign a n u b m w = crossSign a n u (b % 2) m w := by
  unfold crossSign
  refine neg_one_pow_congr ?_
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]

/-- Gluing a bottom piece $P$ (of rank $p$) to top pieces of rank $r - p$: the top pieces with $\nu_P + \nu_T = \nu$,
vanishing below two scales above the cut of $P$. -/
def topSet {r : ℕ} (x : (p : ℕ) × LocGenus v p) (ν : ℕ) : Set (LocGenus v (r - x.1)) :=
  {T | T.Nondeg ∧ ZeroBelow T (cutG x.2 + 2) ∧ νG x.2 + νG T = ν}

section Decomp

variable (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
include h2

theorem f_glueN {r p q : ℕ} {P : LocGenus v p} {T : LocGenus v q} (hP : P.Nondeg) (hT : T.Nondeg)
    (hn : p + q = r) {c : ℕ} (hPc : ZeroFrom P c) (hTc : ZeroBelow T (c + 2)) (ψ : State → ℝ) :
    ψ (st (glueN r P T)) * ((glueN r P T).beta)⁻¹ = kap P q * (ψ (gam P q (st T)) * (T.beta)⁻¹) := by
  have hst : st (glueN r P T) = gam P q (st T) := by
    rw [st_glueN h2 hP hT hn]
    unfold gam st
    simp only [ZMod.val_natCast]
    rw [← crossSign_mod]
  have hb := invBeta_glueN h2 hP hT hn hPc hTc
  rw [hst]
  unfold kap
  have h1 : (2 : ℝ) * 2 ^ (νG P * q) ≠ 0 := by positivity
  field_simp
  linear_combination (ψ (gam P q (st T))) * hb

theorem νG_split {n : ℕ} {G : LocGenus v n} (hG : G.Nondeg) :
    νG G = νG (bottom (pB G) G) + νG (top (n - pB G) G) := by
  have a := isRep_rep h2 hG
  have hb := isRep_bottom h2 hG
  have ht := isRep_top h2 hG
  have hd : dyDim (lowL (cutG G) (rep G) ++ highL (cutG G) (rep G)) = n := by
    rw [dyDim_append, dyDim_low_high h2, a.2.1]
  have hlh : IsRep G (lowL (cutG G) (rep G) ++ highL (cutG G) (rep G)) := by
    refine ⟨hb.1.append ht.1, hd, ?_⟩
    refine ((genusOf_eq_iff' h2 (hb.1.append ht.1) a.1 hd a.2.1).2 ?_).trans a.2.2
    rw [lowL_append_highL]; exact Relation.EqvGen.refl _
  rw [← hlh.valSum_eq h2, valSum_append, hb.valSum_eq h2, ht.valSum_eq h2]

theorem Q_bottom (Q : TwoSymbol → Prop) (hQme : ∀ σ τ, MoveEquiv σ τ → (Q σ ↔ Q τ))
    (hQloc : ∀ σ τ (c : ℕ), (∀ k ≤ c, σ k = τ k) → (∃ k < c, (σ k).dim ≠ 0) → (Q σ ↔ Q τ))
    {n : ℕ} {G : LocGenus v n} (hG : G.Nondeg) (hR : Red G) {p' : ℕ} (hp' : pB G = p') :
    Q (blockSymbol (rep G)) ↔ Q (blockSymbol (rep (bottom p' G))) := by
  subst hp'
  have hb := isRep_bottom h2 hG
  rw [hQme _ _ (hb.moveEquiv h2 (isRep_rep h2 hb.nondeg)).symm, blockSymbol_lowL]
  obtain ⟨k, hk, hne⟩ := (cutF_spec hR.1).1
  refine hQloc _ _ (cutG G) (fun j hj => ?_) ⟨k, hk, hne⟩
  unfold lowS glueS; rw [if_pos hj]

end Decomp

/-- The index set of the bottom pieces of rank $1 \le p < r$. -/
def Idx (v : HeightOneSpectrum (𝓞 ℚ)) (r : ℕ) (Q : TwoSymbol → Prop) : Set ((p : ℕ) × LocGenus v p) :=
  ⋃ p ∈ Finset.Ico 1 r, Sigma.mk p '' IrrSet v p Q

section Decomp2

variable (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
include h2

theorem red_eq (Q : TwoSymbol → Prop) (hQme : ∀ σ τ, MoveEquiv σ τ → (Q σ ↔ Q τ))
    (hQloc : ∀ σ τ (c : ℕ), (∀ k ≤ c, σ k = τ k) → (∃ k < c, (σ k).dim ≠ 0) → (Q σ ↔ Q τ)) (r ν : ℕ) :
    {G | G ∈ Qset v r Q ν ∧ Red G} = ⋃ x ∈ Idx v r Q, glueN r x.2 '' topSet (r := r) x ν := by
  ext G
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, Idx, Set.mem_image, Finset.mem_coe, exists_prop]
  constructor
  · rintro ⟨⟨hN, hQ, hν⟩, hR⟩
    have hp := pB_pos h2 hN hR
    refine ⟨⟨pB G, bottom (pB G) G⟩, ⟨pB G, Finset.mem_Ico.2 hp, bottom (pB G) G,
      ⟨(isRep_bottom h2 hN).nondeg, irred_bottom h2 hN hR, (Q_bottom h2 Q hQme hQloc hN hR rfl).1 hQ⟩, rfl⟩,
      top (r - pB G) G, ⟨(isRep_top h2 hN).nondeg, ?_, ?_⟩, glueN_bottom_top h2 hN hR⟩
    · show ZeroBelow (top (r - pB G) G) (cutG (bottom (pB G) G) + 2)
      rw [cutG_bottom h2 hN hR]; exact zeroBelow_top h2 hN hR
    · show νG (bottom (pB G) G) + νG (top (r - pB G) G) = ν
      rw [← νG_split h2 hN]; exact hν
  · rintro ⟨x, ⟨p, hp, P, hP, rfl⟩, T, ⟨hT, hTz, hν⟩, rfl⟩
    have hp' := Finset.mem_Ico.1 hp
    have hn : p + (r - p) = r := by omega
    have g := isRep_glueN h2 hP.1 hT hn
    obtain ⟨hpB, hbot⟩ := bottom_glueN h2 hP.1 hT hn hP.2.1 hTz
    have hR := red_glueN h2 hP.1 hT hn hP.2.1 hTz (show 1 ≤ r - p by omega)
    refine ⟨⟨g.nondeg, ?_, ?_⟩, hR⟩
    · rw [Q_bottom h2 Q hQme hQloc g.nondeg hR hpB, hbot]; exact hP.2.2
    · rw [← g.valSum_eq h2, valSum_append, (isRep_rep h2 hP.1).valSum_eq h2,
        (isRep_rep h2 hT).valSum_eq h2]; exact hν

theorem red_disjoint (Q : TwoSymbol → Prop) (r ν : ℕ) :
    (Idx v r Q).PairwiseDisjoint fun x => glueN r x.2 '' topSet (r := r) x ν := by
  intro x hx y hy hxy
  refine Set.disjoint_left.2 ?_
  rintro G ⟨T, hT, rfl⟩ ⟨T', hT', hG⟩
  simp only [Idx, Set.mem_iUnion, Set.mem_image, Finset.mem_coe, exists_prop] at hx hy
  obtain ⟨p, hp, P, hP, rfl⟩ := hx
  obtain ⟨p', hp', P', hP', rfl⟩ := hy
  have hn : p + (r - p) = r := by have := Finset.mem_Ico.1 hp; omega
  have hn' : p' + (r - p') = r := by have := Finset.mem_Ico.1 hp'; omega
  obtain ⟨h1, h3⟩ := bottom_glueN h2 hP.1 hT.1 hn hP.2.1 hT.2.1
  obtain ⟨h1', h3'⟩ := bottom_glueN h2 hP'.1 hT'.1 hn' hP'.2.1 hT'.2.1
  rw [hG] at h1' h3'
  have hpp : p = p' := h1.symm.trans h1'
  subst hpp
  exact hxy (by rw [← h3, ← h3'])

end Decomp2

/-! ### Finiteness of the pieces -/

section Fin2

variable (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
include h2

theorem zeroFrom_of_not_red {n : ℕ} {G : LocGenus v n} (hN : G.Nondeg) (hR : ¬ Red G) {M : ℕ}
    (hM : (∃ k ≤ M, dG G k ≠ 0) ∨ ∀ k, dG G k = 0) : ZeroFrom G (M + 2 * n + 2) := by
  rcases hM with hM | hM
  · obtain ⟨N, hN'⟩ := support_finite h2 hN
    obtain ⟨k₀, hk₀', hk₀⟩ := hM
    have hM : ∃ k ≤ M, dG G k ≠ 0 := ⟨k₀, hk₀', hk₀⟩
    have hcut : ∃ c, CutAt (dG G) c := ⟨max N (k₀ + 1), ⟨k₀, by omega, hk₀⟩, hN' _ (by omega), hN' _ (by omega)⟩
    have hI : Irred G := by
      refine ⟨hcut, fun k hk => ?_⟩
      by_contra hne
      rcases Nat.eq_or_lt_of_le hk with h | h
      · exact hne (h ▸ (cutF_spec hcut).2.1)
      · exact hR ⟨hcut, k, h, hne⟩
    exact irred_zeroFrom h2 hN hI hM
  · exact fun k _ => hM k

theorem irrSet_finite (p : ℕ) (Q : TwoSymbol → Prop) (M : ℕ)
    (hQbd : ∀ D, AdmL D → Q (blockSymbol D) → ∃ k ≤ M, (blockSymbol D k).dim ≠ 0) :
    (IrrSet v p Q).Finite := by
  refine (finite_bound h2 p (M + 2 * p + 2)).subset ?_
  rintro P ⟨hN, hI, hQ⟩
  exact ⟨hN, irred_zeroFrom h2 hN hI (hQbd _ (isRep_rep h2 hN).1 hQ)⟩

theorem irrPart_finite (r : ℕ) (Q : TwoSymbol → Prop) (M : ℕ)
    (hQbd : ∀ D, AdmL D → Q (blockSymbol D) → ∃ k ≤ M, (blockSymbol D k).dim ≠ 0) :
    {G : LocGenus v r | G.Nondeg ∧ Q (blockSymbol (rep G)) ∧ ¬ Red G}.Finite := by
  refine (finite_bound h2 r (M + 2 * r + 2)).subset ?_
  rintro G ⟨hN, hQ, hR⟩
  exact ⟨hN, zeroFrom_of_not_red h2 hN hR (Or.inl (hQbd _ (isRep_rep h2 hN).1 hQ))⟩

theorem idx_finite (r : ℕ) (Q : TwoSymbol → Prop) (M : ℕ)
    (hQbd : ∀ D, AdmL D → Q (blockSymbol D) → ∃ k ≤ M, (blockSymbol D k).dim ≠ 0) :
    (Idx v r Q).Finite :=
  (Finset.finite_toSet _).biUnion fun p _ => (irrSet_finite h2 p Q M hQbd).image _

end Fin2

/-! ### Rationality -/

section Rat

variable (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
include h2

/-- **The decomposition of the series by bottom pieces** (coefficientwise). -/
theorem coef_decomp {r : ℕ} (Q : TwoSymbol → Prop) (hQme : ∀ σ τ, MoveEquiv σ τ → (Q σ ↔ Q τ))
    (hQloc : ∀ σ τ (c : ℕ), (∀ k ≤ c, σ k = τ k) → (∃ k < c, (σ k).dim ≠ 0) → (Q σ ↔ Q τ)) (M : ℕ)
    (hQbd : ∀ D, AdmL D → Q (blockSymbol D) → ∃ k ≤ M, (blockSymbol D k).dim ≠ 0) (ψ : State → ℝ) (ν : ℕ) :
    coefS (Qset v r Q) ψ ν =
      (∑ G ∈ (irrPart_finite h2 r Q M hQbd).toFinset, if νG G = ν then ψ (st G) * (G.beta)⁻¹ else 0) +
      ∑ x ∈ (idx_finite h2 r Q M hQbd).toFinset, kap x.2 (r - x.1) *
        (if νG x.2 ≤ ν then coefS (Uset v (r - x.1) (cutG x.2 + 2)) (fun s => ψ (gam x.2 (r - x.1) s))
          (ν - νG x.2) else 0) := by
  unfold coefS
  have hfin : (Qset v r Q ν).Finite := finite_sub h2 _ ν fun G hG => ⟨hG.1, hG.2.2⟩
  rw [← finsum_mem_inter_add_sdiff {G : LocGenus v r | ¬ Red G} hfin]
  congr 1
  · rw [finsum_mem_eq_finite_toFinset_sum _ (hfin.inter_of_left _), ← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext G
    simp only [Set.Finite.mem_toFinset, Finset.mem_filter, Set.mem_inter_iff, Set.mem_setOf_eq, Qset]
    tauto
  · have e : Qset v r Q ν \ {G | ¬ Red G} = {G | G ∈ Qset v r Q ν ∧ Red G} := by
      ext G; simp
    rw [e, red_eq h2 Q hQme hQloc r ν, finsum_mem_biUnion (red_disjoint h2 Q r ν) (idx_finite h2 r Q M hQbd)
      (fun x hx => finite_sub h2 _ ν fun G hG => by
        have hm : G ∈ {G | G ∈ Qset v r Q ν ∧ Red G} := by
          rw [red_eq h2 Q hQme hQloc r ν]; exact Set.mem_biUnion hx hG
        exact ⟨hm.1.1, hm.1.2.2⟩),
      finsum_mem_eq_finite_toFinset_sum _ (idx_finite h2 r Q M hQbd)]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Set.Finite.mem_toFinset] at hx
    simp only [Idx, Set.mem_iUnion, Set.mem_image, Finset.mem_coe, exists_prop] at hx
    obtain ⟨p, hp, P, hP, rfl⟩ := hx
    have hn : p + (r - p) = r := by have := Finset.mem_Ico.1 hp; omega
    rw [finsum_mem_image (fun T hT T' hT' h => by
      have := top_glueN h2 hP.1 hT.1 hn hP.2.1 hT.2.1
      rw [h, top_glueN h2 hP.1 hT'.1 hn hP.2.1 hT'.2.1] at this
      exact this.symm)]
    rw [finsum_mem_congr rfl fun T hT => f_glueN h2 hP.1 hT.1 hn hP.2.1.2 hT.2.1 ψ, ← mul_finsum_mem]
    congr 1
    split_ifs with hν
    · refine finsum_mem_congr ?_ fun _ _ => rfl
      ext T
      simp only [topSet, Uset, Set.mem_setOf_eq]
      constructor
      · rintro ⟨a, b, c⟩
        refine ⟨a, b, ?_⟩
        have hν' : νG P ≤ ν := hν
        have c' : νG P + νG T = ν := c
        omega
      · rintro ⟨a, b, c⟩
        refine ⟨a, b, ?_⟩
        have hν' : νG P ≤ ν := hν
        have c' : νG T = ν - νG P := c
        show νG P + νG T = ν
        omega
    · rw [show topSet (r := r) ⟨p, P⟩ ν = ∅ by
        ext T
        simp only [topSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨-, -, hc⟩
        apply hν
        have hc' : νG P + νG T = ν := hc
        show νG P ≤ ν
        omega]
      simp

/-- **Rationality for a predicate determined by the bottom piece**, given rationality in lower ranks. -/
theorem ratQ {r : ℕ} (Q : TwoSymbol → Prop) (hQme : ∀ σ τ, MoveEquiv σ τ → (Q σ ↔ Q τ))
    (hQloc : ∀ σ τ (c : ℕ), (∀ k ≤ c, σ k = τ k) → (∃ k < c, (σ k).dim ≠ 0) → (Q σ ↔ Q τ)) (M : ℕ)
    (hQbd : ∀ D, AdmL D → Q (blockSymbol D) → ∃ k ≤ M, (blockSymbol D k).dim ≠ 0)
    (IH : ∀ q, 1 ≤ q → q < r → ∀ m (ψ : State → ℝ), RatSeries (serS (Qset v q (QE m)) ψ))
    (ψ : State → ℝ) : RatSeries (serS (Qset v r Q) ψ) := by
  have e : serS (Qset v r Q) ψ =
      (∑ G ∈ (irrPart_finite h2 r Q M hQbd).toFinset,
        PowerSeries.C (ψ (st G) * (G.beta)⁻¹) * PowerSeries.X ^ (νG G) * 1) +
      ∑ x ∈ (idx_finite h2 r Q M hQbd).toFinset, PowerSeries.C (kap x.2 (r - x.1)) *
        PowerSeries.X ^ (νG x.2) * serS (Uset v (r - x.1) (cutG x.2 + 2)) (fun s => ψ (gam x.2 (r - x.1) s)) := by
    ext ν
    rw [serS, PowerSeries.coeff_mk, coef_decomp h2 Q hQme hQloc M hQbd ψ ν, map_add, map_sum, map_sum]
    congr 1
    · refine Finset.sum_congr rfl fun G _ => ?_
      rw [mul_one, PowerSeries.coeff_C_mul_X_pow]
      split_ifs <;> first | rfl | (exfalso; omega)
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
      split_ifs <;> simp [serS]
  rw [e]
  refine (RatSeries.sum _ _ fun G _ => RatSeries.CXpowMul _ _ (by simpa using RatSeries.const 1)).add
    (RatSeries.sum _ _ fun x hx => RatSeries.CXpowMul _ _ ?_)
  rw [Set.Finite.mem_toFinset] at hx
  simp only [Idx, Set.mem_iUnion, Set.mem_image, Finset.mem_coe, exists_prop] at hx
  obtain ⟨p, hp, P, hP, rfl⟩ := hx
  have hp' := Finset.mem_Ico.1 hp
  exact ratU_of h2 (r := r - p) (by omega) _ (by omega) _ fun m => IH (r - p) (by omega) (by omega) m _

omit h2 in
theorem QE_me (m : ℕ) : ∀ σ τ, MoveEquiv σ τ → (QE m σ ↔ QE m τ) := by
  intro σ τ h
  unfold QE
  simp only [h.sameInvariants.dim_eq]

omit h2 in
theorem QE_loc (m : ℕ) : ∀ σ τ (c : ℕ), (∀ k ≤ c, σ k = τ k) → (∃ k < c, (σ k).dim ≠ 0) →
    (QE m σ ↔ QE m τ) := by
  intro σ τ c h ⟨k, hk, hne⟩
  unfold QE
  by_cases hm : m ≤ c
  · constructor
    · rintro ⟨h1, h3⟩; exact ⟨fun j hj => by rw [← h j (by omega)]; exact h1 j hj, by rw [← h m hm]; exact h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨fun j hj => by rw [h j (by omega)]; exact h1 j hj, by rw [h m hm]; exact h3⟩
  · constructor
    · rintro ⟨h1, -⟩; exact absurd (h1 k (by omega)) hne
    · rintro ⟨h1, -⟩; exact absurd (h1 k (by omega)) (by rw [← h k (by omega)]; exact hne)

/-- **Rationality of the series of the genera of lowest scale $2^m$**, every rank. -/
theorem ratE : ∀ (r m : ℕ) (ψ : State → ℝ), RatSeries (serS (Qset v r (QE m)) ψ) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro m ψ
    exact ratQ h2 (QE m) (QE_me m) (QE_loc m) m (fun D _ hQ => ⟨m, le_rfl, hQ.2⟩)
      (fun q _ hq m' ψ' => ih q hq m' ψ') ψ

end Rat

/-! ### Primitivity and the true local genera -/

/-- The symbol of a primitive form: a nonzero constituent of scale $1$ or a type I constituent of scale $2$. -/
def QP (σ : TwoSymbol) : Prop := (σ 0).dim ≠ 0 ∨ IsTypeI σ 1

theorem QP_me : ∀ σ τ, MoveEquiv σ τ → (QP σ ↔ QP τ) := by
  intro σ τ h
  unfold QP
  rw [h.sameInvariants.dim_eq, MoveEquiv.isTypeI_iff h]

theorem QP_loc : ∀ σ τ (c : ℕ), (∀ k ≤ c, σ k = τ k) → (∃ k < c, (σ k).dim ≠ 0) → (QP σ ↔ QP τ) := by
  intro σ τ c h hex
  unfold QP IsTypeI
  rw [h 0 (by omega), h 1 (by omega)]

theorem QP_bd : ∀ D, AdmL D → QP (blockSymbol D) → ∃ k ≤ 1, (blockSymbol D k).dim ≠ 0 := by
  rintro D - (h | h)
  · exact ⟨0, by omega, h⟩
  · obtain ⟨b, hb, hbk, -⟩ := (isTypeI_blockSymbol_iff D 1).1 h
    exact ⟨1, le_rfl, (dim_blockSymbol_ne_zero_iff D 1).2 ⟨b, hb, hbk⟩⟩

theorem prim_iff_QP (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {n : ℕ} {G : LocGenus v n} (hN : G.Nondeg) :
    G.Prim ↔ QP (blockSymbol (rep G)) := by
  have a := isRep_rep h2 hN
  conv_lhs => rw [← a.2.2]
  rw [prim_genusOf_iff v h2 a.2.1, isPrimBlocks_iff a.1]
  unfold QP
  rw [dim_blockSymbol_ne_zero_iff, isTypeI_blockSymbol_iff]
  constructor
  · rintro ⟨b, hb, hP⟩
    cases b with
    | sq e u => exact Or.inr ⟨_, hb, by simp only [BlockPrim] at hP; simp [blockExp, hP], trivial⟩
    | hyp e => exact Or.inl ⟨_, hb, by simp only [BlockPrim] at hP; simp [blockExp, hP]⟩
    | ell e => exact Or.inl ⟨_, hb, by simp only [BlockPrim] at hP; simp [blockExp, hP]⟩
  · rintro (⟨b, hb, hbk⟩ | ⟨b, hb, hbk, hsq⟩)
    · refine ⟨b, hb, ?_⟩
      have hev := a.1.2.2 b hb
      cases b with
      | sq e u => exact absurd (show e = 0 by simpa [blockExp] using hbk) hev
      | hyp e => simpa [BlockPrim, blockExp] using hbk
      | ell e => simpa [BlockPrim, blockExp] using hbk
    · refine ⟨b, hb, ?_⟩
      cases b with
      | sq e u => simpa [BlockPrim, blockExp] using hbk
      | hyp e => exact absurd hsq id
      | ell e => exact absurd hsq id

/-- The indicator of "unit class $w$ and Hasse invariant $\varepsilon$". -/
def psiW (w : ZMod 8) (ε : ℤ) (s : State) : ℝ := open Classical in if s.2.1 = w ∧ s.2.2 = ε then 1 else 0

/-- **The mass sum over $\mathrm{Gen}^*_2([2^\nu w], \varepsilon; n)$ is a coefficient of a generating series.** -/
theorem sum_genStar_two (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {n : ℕ} {w : ℤ} (hw : Odd w) (G₀ : LocGenus v n) (ν : ℕ)
    (ε : ℤ) :
    ∑ᶠ G ∈ {G : LocGenus v n | G.IsGenStar (zSqCl v (2 ^ ν * w)) ε}, G₀.beta / G.beta =
      G₀.beta * coefS (Qset v n QP) (psiW ((w : ℤ) : ZMod 8) ε) ν := by
  unfold coefS
  have hfin : (Qset v n QP ν).Finite := finite_sub h2 _ ν fun G hG => ⟨hG.1, hG.2.2⟩
  rw [← finsum_mem_inter_add_sdiff {G : LocGenus v n | uG G = ((w : ℤ) : ZMod 8) ∧ G.hasse = ε} hfin]
  have h0 : ∑ᶠ G ∈ Qset v n QP ν \ {G : LocGenus v n | uG G = ((w : ℤ) : ZMod 8) ∧ G.hasse = ε},
      psiW ((w : ℤ) : ZMod 8) ε (st G) * (G.beta)⁻¹ = 0 := by
    refine finsum_mem_eq_zero_of_forall_eq_zero fun G hG => ?_
    have hnot : ¬ (uG G = ((w : ℤ) : ZMod 8) ∧ G.hasse = ε) := hG.2
    simp [psiW, st, hnot]
  rw [h0, add_zero, mul_finsum_mem]
  · refine finsum_mem_congr ?_ fun G hG => ?_
    · ext G
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Qset, LocGenus.IsGenStar]
      constructor
      · rintro ⟨hN, hP, hd, hh⟩
        have a := isRep_rep h2 hN
        rw [a.det_eq_iff h2 hw] at hd
        exact ⟨⟨hN, (prim_iff_QP h2 hN).1 hP, hd.1⟩, hd.2, hh⟩
      · rintro ⟨⟨hN, hP, hν⟩, hu, hh⟩
        have a := isRep_rep h2 hN
        exact ⟨hN, (prim_iff_QP h2 hN).2 hP, (a.det_eq_iff h2 hw ν).2 ⟨hν, hu⟩, hh⟩
    · have this : uG G = ((w : ℤ) : ZMod 8) ∧ G.hasse = ε := hG.2
      simp [psiW, st, this, div_eq_mul_inv]

/-- **The normalized local mass sum $A^*_{2;n}(S)$ of the true local genera** (Def. 4.6): the sum of
$\beta(G_0)/\beta(G)$ over the nondegenerate primitive local genera $G$ with $\det_H G = S$ (both Hasse invariants).
The same definition as at odd primes (`RatOdd.trueAstar`). -/
abbrev trueAstar2 (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) (G₀ : LocGenus v n) (S : LocalSqCl v) : ℝ :=
  RatOdd.trueAstar v n G₀ S

/-- **The normalized local mass sum $B^*_{2;n}(S)$** (Hasse invariant as a sign); `RatOdd.trueBstar`. -/
abbrev trueBstar2 (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) (G₀ : LocGenus v n) (S : LocalSqCl v) : ℝ :=
  RatOdd.trueBstar v n G₀ S

/-- **Theorem 5.4 (for $A^*$) at $p = 2$, every rank $n$, $F = \mathbb Q$, true local genera.**  For $v$ the prime
of $\mathbb Q$ above $2$ (`h2`), every number of variables $n$, every odd integer $w$ (the fixed unit class
$[w] \in \mathbb Z_2^\times/(\mathbb Z_2^\times)^2$) and every reference genus $G_0$, the fixed-unit series
$\sum_\nu A^*_{2;n}([2^\nu w])\,X^\nu$, $X = 2^{-s}$, is a rational function of $X$: $P/Q$ for polynomials $P$, $Q$
with $Q(0) \ne 0$.  Unconditional. -/
@[kb "hanke2011structure" "Thm. 5.4, p. 23-24 (p = 2, every n, F = Q)"]
theorem theorem_5_4_two_A_rank (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {n : ℕ} {w : ℤ} (hw : Odd w) (G₀ : LocGenus v n) :
    RatSeries (PowerSeries.mk fun ν : ℕ => trueAstar2 v n G₀ (zSqCl v (2 ^ ν * w))) := by
  have e : (PowerSeries.mk fun ν : ℕ => trueAstar2 v n G₀ (zSqCl v (2 ^ ν * w))) =
      PowerSeries.C G₀.beta * PowerSeries.X ^ 0 *
        (serS (Qset v n QP) (psiW ((w : ℤ) : ZMod 8) 1) + serS (Qset v n QP) (psiW ((w : ℤ) : ZMod 8) (-1))) := by
    ext ν
    rw [PowerSeries.coeff_mk, trueAstar2, RatOdd.trueAstar, sum_genStar_two h2 hw, sum_genStar_two h2 hw]
    simp [serS, PowerSeries.coeff_mk, mul_add]
  rw [e]
  exact RatSeries.CXpowMul _ 0 ((ratQ h2 QP QP_me QP_loc 1 QP_bd (fun q _ _ m ψ => ratE h2 q m ψ) _).add
    (ratQ h2 QP QP_me QP_loc 1 QP_bd (fun q _ _ m ψ => ratE h2 q m ψ) _))

/-- **Theorem 5.4 (for $B^*$) at $p = 2$, every rank $n$, $F = \mathbb Q$, true local genera**: the fixed-unit series
$\sum_\nu B^*_{2;n}([2^\nu w])\,X^\nu$ is a rational function of $X = 2^{-s}$ (same hypotheses as
`theorem_5_4_two_A_rank`).  Unconditional. -/
@[kb "hanke2011structure" "Thm. 5.4, p. 23-24 (p = 2, every n, F = Q)"]
theorem theorem_5_4_two_B_rank (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {n : ℕ} {w : ℤ} (hw : Odd w) (G₀ : LocGenus v n) :
    RatSeries (PowerSeries.mk fun ν : ℕ => trueBstar2 v n G₀ (zSqCl v (2 ^ ν * w))) := by
  have e : (PowerSeries.mk fun ν : ℕ => trueBstar2 v n G₀ (zSqCl v (2 ^ ν * w))) =
      PowerSeries.C G₀.beta * PowerSeries.X ^ 0 *
        (serS (Qset v n QP) (psiW ((w : ℤ) : ZMod 8) 1) +
          PowerSeries.C (-1) * PowerSeries.X ^ 0 * serS (Qset v n QP) (psiW ((w : ℤ) : ZMod 8) (-1))) := by
    ext ν
    rw [PowerSeries.coeff_mk, trueBstar2, RatOdd.trueBstar, sum_genStar_two h2 hw, sum_genStar_two h2 hw]
    simp [serS, PowerSeries.coeff_mk, mul_add]
    ring
  rw [e]
  exact RatSeries.CXpowMul _ 0 ((ratQ h2 QP QP_me QP_loc 1 QP_bd (fun q _ _ m ψ => ratE h2 q m ψ) _).add
    (RatSeries.CXpowMul (-1) 0 (ratQ h2 QP QP_me QP_loc 1 QP_bd (fun q _ _ m ψ => ratE h2 q m ψ) _)))

/-- **Corollary 5.5 for $A^*$ at $p = 2$, every rank $n$, $F = \mathbb Q$** (distinguished family
$\lambda(2^i) = 2^i$): the Euler factor $\sum_i A^*_{2;n}([2^i])\,2^{-is}$ is a rational function of $2^{-s}$. -/
@[kb "hanke2011structure" "Cor. 5.5, p. 24 (A*, p = 2, every n, F = Q, lambda(2^i) = 2^i)"]
theorem cor_5_5_two_A_rank (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {n : ℕ} (G₀ : LocGenus v n) :
    RatSeries (PowerSeries.mk fun i : ℕ => trueAstar2 v n G₀ (zSqCl v (2 ^ i))) := by
  simpa only [mul_one] using theorem_5_4_two_A_rank h2 (w := 1) odd_one G₀

/-- **Corollary 5.5 for $B^*$ at $p = 2$, every rank $n$, $F = \mathbb Q$** ($\lambda(2^i) = 2^i$). -/
@[kb "hanke2011structure" "Cor. 5.5, p. 24 (B*, p = 2, every n, F = Q, lambda(2^i) = 2^i)"]
theorem cor_5_5_two_B_rank (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {n : ℕ} (G₀ : LocGenus v n) :
    RatSeries (PowerSeries.mk fun i : ℕ => trueBstar2 v n G₀ (zSqCl v (2 ^ i))) := by
  simpa only [mul_one] using theorem_5_4_two_B_rank h2 (w := 1) odd_one G₀

end

end QuadFormsKB.Hanke2011Structure.RatTwo
