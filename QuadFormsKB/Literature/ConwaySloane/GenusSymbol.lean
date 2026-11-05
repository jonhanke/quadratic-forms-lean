/-
# Conway–Sloane, Ch. 15, §7.8: the genus symbol

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §7.8, p. 384
(`conwaysloane1999`). The genus symbol $\mathrm I_{r,s}(\cdots)$ or $\mathrm{II}_{r,s}(\cdots)$ omits the constituents of
scale $1$: "the omitted $1$-constituents can be recovered from the determinant, dimension, type and oddity formula".

**Proves** `GenusSymbolData.scaleOne_determined`: two systems of symbols satisfying (29)–(35) with the same dimension,
determinant, $(-1)$-adic symbol, the same constituents at every scale $q > 1$ and the same type of the 2-adic constituent
of scale $1$ have the same constituents of scale $1$ (at every odd prime and at $2$). The dimension comes from the
dimension, the sign from (29), and (type I) the oddity from (30). Both systems are taken with the same bound $N$.
-/
import QuadFormsKB.Literature.ConwaySloane.Theorem11

namespace QuadFormsKB.ConwaySloane

open Finset

theorem sum_range_eq_of_succ {M : Type*} [AddCancelCommMonoid M] {N : ℕ} (f g : ℕ → M) (hfg : ∀ k, 1 ≤ k → f k = g k)
    (h : ∑ k ∈ range N, f k = ∑ k ∈ range N, g k) (hN : 1 ≤ N) : f 0 = g 0 := by
  obtain ⟨M', rfl⟩ : ∃ M', N = M' + 1 := ⟨N - 1, by omega⟩
  rw [sum_range_succ', sum_range_succ'] at h
  have : ∑ k ∈ range M', f (k + 1) = ∑ k ∈ range M', g (k + 1) :=
    sum_congr rfl fun k _ => hfg (k + 1) (by omega)
  rw [this] at h
  exact add_left_cancel h

theorem prod_range_eq_of_succ {N : ℕ} (f g : ℕ → ℤ) (hf : ∀ k, f k = 1 ∨ f k = -1) (hfg : ∀ k, 1 ≤ k → f k = g k)
    (h : ∏ k ∈ range N, f k = ∏ k ∈ range N, g k) (hN : 1 ≤ N) : f 0 = g 0 := by
  obtain ⟨M', rfl⟩ : ∃ M', N = M' + 1 := ⟨N - 1, by omega⟩
  rw [prod_range_succ', prod_range_succ'] at h
  have : ∏ k ∈ range M', f (k + 1) = ∏ k ∈ range M', g (k + 1) :=
    prod_congr rfl fun k _ => hfg (k + 1) (by omega)
  rw [this] at h
  have hne : ∏ k ∈ range M', g (k + 1) ≠ 0 := by
    rw [← this]
    exact prod_ne_zero_iff.mpr fun k _ => by rcases hf (k + 1) with h | h <;> rw [h] <;> decide
  exact mul_left_cancel₀ hne h

theorem toInt_pm (s : Sign) : s.toInt = 1 ∨ s.toInt = -1 := by cases s <;> simp [Sign.toInt]

/-- **The constituents of scale $1$ are determined** by the rest of the genus symbol (Conway–Sloane, §7.8, p. 384). -/
@[kb "conwaysloane1999" "Ch. 15, §7.8, p. 384"]
theorem GenusSymbolData.scaleOne_determined (G G' : GenusSymbolData) (hG : G.Conditions) (hG' : G'.Conditions)
    (hn : G.n = G'.n) (hd : G.det = G'.det) (hr : G.real = G'.real) (hN : G.N = G'.N)
    (hodd : ∀ p k, 1 ≤ k → G.odd p k = G'.odd p k) (htwo : ∀ k, 1 ≤ k → G.two k = G'.two k)
    (htype : (G.two 0).type = (G'.two 0).type) :
    (∀ p, p.Prime → p ≠ 2 → G.odd p 0 = G'.odd p 0) ∧ G.two 0 = G'.two 0 := by
  classical
  -- the case `N = 0`: everything is trivial
  rcases Nat.eq_zero_or_pos G.N with hN0 | hN1
  · refine ⟨fun p _ _ => by rw [hG.odd_supp p 0 (by omega), hG'.odd_supp p 0 (by omega)],
      by rw [hG.two_supp 0 (by omega), hG'.two_supp 0 (by omega)]⟩
  have hdimO : ∀ p, p.Prime → p ≠ 2 → (G.odd p 0).dim = (G'.odd p 0).dim := by
    intro p hp hp2
    refine sum_range_eq_of_succ (N := G.N) (fun k => (G.odd p k).dim) (fun k => (G'.odd p k).dim)
      (fun k hk => by rw [hodd p k hk]) ?_ hN1
    rw [hG.odd_dim p hp hp2, hN, hG'.odd_dim p hp hp2, hn]
  have hsignO : ∀ p, p.Prime → p ≠ 2 → (G.odd p 0).sign = (G'.odd p 0).sign := by
    intro p hp hp2
    apply toInt_injective
    refine prod_range_eq_of_succ (N := G.N) (fun k => (G.odd p k).sign.toInt) (fun k => (G'.odd p k).sign.toInt)
      (fun k => toInt_pm _) (fun k hk => by rw [hodd p k hk]) ?_ hN1
    rw [← toInt_signProd, ← toInt_signProd, (hG.odd_det p hp hp2).2, hN, (hG'.odd_det p hp hp2).2, hd]
  have hdimT : (G.two 0).dim = (G'.two 0).dim := by
    refine sum_range_eq_of_succ (N := G.N) (fun k => (G.two k).dim) (fun k => (G'.two k).dim)
      (fun k hk => by rw [htwo k hk]) ?_ hN1
    rw [hG.two_dim, hN, hG'.two_dim, hn]
  have hsignT : (G.two 0).sign = (G'.two 0).sign := by
    apply toInt_injective
    refine prod_range_eq_of_succ (N := G.N) (fun k => (G.two k).sign.toInt) (fun k => (G'.two k).sign.toInt)
      (fun k => toInt_pm _) (fun k hk => by rw [htwo k hk]) ?_ hN1
    rw [← toInt_signProd, ← toInt_signProd, hG.two_det.2, hN, hG'.two_det.2, hd]
  -- the oddity, from the oddity formula (30)
  have hpex : ∀ p, (G.odd p).pExcess p G.N = (G'.odd p).pExcess p G'.N := by
    intro p
    rw [← hN]
    unfold OddSymbol.pExcess
    obtain ⟨M', hM'⟩ : ∃ M', G.N = M' + 1 := ⟨G.N - 1, by omega⟩
    rw [hM', sum_range_succ', sum_range_succ']
    congr 1
    · exact sum_congr rfl fun k _ => by rw [hodd p (k + 1) (by omega)]
    · simp [ind8]
  have hoddT : (G.two 0).oddity = (G'.two 0).oddity := by
    have h1 := hG.oddity_formula
    have h2 := hG'.oddity_formula
    have hsig : G.signature = G'.signature := by unfold GenusSymbolData.signature; rw [hr]
    have hS : ∑ p ∈ (G.det.natAbs.primeFactors.filter (· ≠ 2)), (G.odd p).pExcess p G.N =
        ∑ p ∈ (G'.det.natAbs.primeFactors.filter (· ≠ 2)), (G'.odd p).pExcess p G'.N := by
      rw [hd]; exact sum_congr rfl fun p _ => hpex p
    have hodd2 : G.two.oddity G.N = G'.two.oddity G'.N := by rw [← h1, ← h2, hsig, hS]
    unfold TwoSymbol.oddity at hodd2
    rw [← hN] at hodd2
    obtain ⟨M', hM'⟩ : ∃ M', G.N = M' + 1 := ⟨G.N - 1, by omega⟩
    rw [hM', sum_range_succ', sum_range_succ'] at hodd2
    have : ∑ k ∈ range M', ((G.two (k + 1)).oddity + 4 * ind8 (Odd (k + 1) ∧ (G.two (k + 1)).sign = .minus)) =
        ∑ k ∈ range M', ((G'.two (k + 1)).oddity + 4 * ind8 (Odd (k + 1) ∧ (G'.two (k + 1)).sign = .minus)) :=
      sum_congr rfl fun k _ => by rw [htwo (k + 1) (by omega)]
    rw [this] at hodd2
    have := add_left_cancel hodd2
    simpa [ind8] using this
  refine ⟨fun p hp hp2 => ?_, ?_⟩
  · have h1 := hdimO p hp hp2
    have h2 := hsignO p hp hp2
    cases h : G.odd p 0; cases h' : G'.odd p 0
    simp_all
  · cases h : G.two 0; cases h' : G'.two 0
    simp_all

end QuadFormsKB.ConwaySloane
