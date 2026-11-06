/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import Mathlib
import QuadFormsKB.Literature.Hanke2011Structure.RationalityNondyadicGenusNF
import QuadFormsKB.Literature.Hanke2011Structure.RationalityOddMass
import QuadFormsKB.Literature.Hanke2011Structure.RationalityOddStats

/-!
# Paper 6, Lemma 7.3 and Remark 7.4 at a nondyadic prime of a number field

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (`hanke2011structure`), Lemma 7.3 and Remark 7.4, p. 29.

For $\mathfrak p \nmid 2$ of a number field $F$, $q = |\mathcal O_F/\mathfrak p|$, the paper's $\mathfrak p$-mass
$m_{\mathfrak p}$ is Conway–Sloane's formula (3) (`conwaysloane1988`, p. 263) with $p$ replaced by $q$
(`pMassNF`).  We prove, for the genus $G = D(z,x)$ of $\operatorname{diag}(\pi^{z_i}\operatorname{rep}(x_i))$
(`genND`; every nondegenerate local genus has this form, `exists_genND`), of rank $n$ and
$\nu = \sum_i z_i = \operatorname{ord}_{\mathfrak p}\det_H$:
$$\beta(G)^{-1} = 2\,m_{\mathfrak p}(G)\,q^{-(n+1)\nu/2}.$$
Indices are 0-based.
-/

open Finset Matrix IsDedekindDomain NumberField

namespace QuadFormsKB.Hanke2011Structure.Lemma73NF

open QuadFormsKB QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR QuadFormsKB.Hanke2011Structure
  QuadFormsKB.Hanke2011Structure.RatOdd QuadFormsKB.Hanke2011Structure.RatND QuadFormsKB.ConwaySloane
  QuadFormsKB.ConwaySloane.Mass QuadFormsKB.Odd7

noncomputable section

/-- **The $\mathfrak p$-mass of the paper (Lemma 7.3, Remark 7.4), $\mathfrak p \nmid 2$:** Conway–Sloane's
formula (3) (`conwaysloane1988`, p. 263) with $p$ replaced by $q = N(\mathfrak p)$:
$$m_{\mathfrak p}(\sigma) = \prod_{k<N} M_q(n_k,\varepsilon_k)\cdot\sqrt q^{\,\sum_{k<k'<N}(k'-k)n_kn_{k'}},$$
for an odd symbol $\sigma$ with $k$-th constituent of dimension $n_k$ (`dim`) and sign $\varepsilon_k$ (`sign`),
trivial from index $N$ on; $e = \chi(-1) \in \{\pm1\}$ is the quadratic character of the residue field at $-1$ and
$M_q = P_q^{-1}$ is the diagonal factor (`Mq`) of the species of the constituent. -/
@[kb "hanke2011structure" "Lemma 7.3, p. 29 (m_p: CS (3) with q); conwaysloane1988 (3), p. 263"]
def pMassNF (q : ℕ) (e : ℤˣ) (σ : OddSymbol) (N : ℕ) : ℝ :=
  (∏ k ∈ range N, Mq q e (σ k).dim (σ k).sign) * Real.sqrt q ^ crossExp (fun k => (σ k).dim) N

/-- The weight identity for an arbitrary factor weight `M` and `a ρ = q^{-ρ(ρ+1)/2}` (the proof of
`RatOdd.wtN_mul_pow`, which only uses `M 0 plus = 1`-free algebra). -/
theorem wtN_mul_pow_q (q : ℕ) (hq : 0 < q) (M : ℕ → Sign → ℝ) :
    ∀ (N : ℕ) (σ : OddSymbol),
      wtN M (aq q) N σ * Real.sqrt q ^ ((rk σ N + 1) * zs σ N) =
        (∏ k ∈ range N, M (σ k).dim (σ k).sign) * Real.sqrt q ^ crossExp (fun k => (σ k).dim) N := by
  intro N
  induction N with
  | zero => intro σ; simp [wtN_zero, rk, zs, crossExp]
  | succ N ih =>
    intro σ
    have hih := ih (shiftS σ)
    have hs0 : Real.sqrt q ≠ 0 := (Real.sqrt_pos.2 (Nat.cast_pos.2 hq)).ne'
    have haq : ∀ ρ, aq q ρ = ((Real.sqrt q) ^ (ρ * (ρ + 1)))⁻¹ := fun ρ => aw_eq q hq ρ
    rw [wtN_succ, rk_succ, zs_succ, Finset.prod_range_succ', RatOdd.crossExp_succ, sum_succ_dim, haq]
    have e1 : crossExp (fun k => (σ (k + 1)).dim) N = crossExp (fun k => (shiftS σ k).dim) N := rfl
    have e2 : ∏ k ∈ range N, M (σ (k + 1)).dim (σ (k + 1)).sign =
        ∏ k ∈ range N, M (shiftS σ k).dim (shiftS σ k).sign := rfl
    simp only [e1, e2]
    set s := Real.sqrt q
    set R := rk (shiftS σ) N
    set Z := zs (shiftS σ) N
    set d := (σ 0).dim
    set W := wtN M (aq q) N (shiftS σ)
    set Pr := ∏ k ∈ range N, M (shiftS σ k).dim (shiftS σ k).sign
    set c := crossExp (fun k => (shiftS σ k).dim) N
    have key : s ^ ((d + R + 1) * (Z + R)) = s ^ (R * (R + 1)) * s ^ ((R + 1) * Z) * s ^ (d * (Z + R)) := by
      rw [← pow_add, ← pow_add]; congr 1; ring
    have hA : s ^ (R * (R + 1)) ≠ 0 := pow_ne_zero _ hs0
    rw [key, pow_add s c (d * (Z + R))]
    generalize s ^ (R * (R + 1)) = A at hA ⊢
    generalize s ^ ((R + 1) * Z) = B at hih ⊢
    generalize s ^ (d * (Z + R)) = C
    generalize s ^ c = D at hih ⊢
    calc M d (σ 0).sign * A⁻¹ * W * (A * B * C) = M d (σ 0).sign * (W * B) * C := by
          field_simp
      _ = _ := by rw [hih]; ring

/-- **The weight of a finitely supported symbol is its $q$-mass over $\sqrt q^{(r+1)\nu}$:**
$\mathrm{wt}(\sigma)\,\sqrt q^{(r+1)\nu} = m_{\mathfrak p}(\sigma)$, with $r = \sum n_k$, $\nu = \sum k n_k$. -/
theorem wtC_mul_pow_q (q : ℕ) (hq : 0 < q) (e : ℤˣ) {σ : OddSymbol} {N : ℕ} (h : TrivFrom σ N) :
    wtC (Mq q e) (aq q) σ * Real.sqrt q ^ ((rkC σ + 1) * zsC σ) = pMassNF q e σ N := by
  have h1 := wtN_mul_pow_q q hq (Mq q e) N σ
  unfold wtC rkC zsC
  rw [(stable_wtN (Mq q e) (aq q) (Mq_zero q e) (aq_zero q)).cut_eq h, stable_rk.cut_eq h, stable_zs.cut_eq h, h1]
  rfl

/-! ### Comparison with Conway–Sloane's $p$-mass over $\mathbb Q$ -/

theorem sign_aux (p : ℕ) (e : ℤˣ) (he : (e : ℤ) = if p % 4 = 3 then -1 else 1) (m : ℕ) (s : Sign) :
    ((if m % 2 = 1 ∧ p % 4 = 3 then s.flip else s).toInt : ℤ) = ((e ^ m * signU s : ℤˣ) : ℤ) := by
  have he' : e = if p % 4 = 3 then -1 else 1 := by
    apply Units.ext; rw [he]; split_ifs <;> simp
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · have h0 : m % 2 = 0 := by omega
    have hm : e ^ m = 1 := by
      rw [hk, ← two_mul, pow_mul]; rcases Int.units_eq_one_or e with h | h <;> simp [h]
    simp only [h0, hm]
    cases s <;> simp [signU, Sign.toInt]
  · have h1 : m % 2 = 1 := by omega
    by_cases h3 : p % 4 = 3
    · have he1 : e = -1 := by rw [he', if_pos h3]
      have hm : e ^ m = -1 := by rw [he1]; exact Odd.neg_one_pow ⟨k, hk⟩
      simp only [h1, h3, and_self, if_true, hm]
      cases s <;> simp [signU, Sign.toInt, Sign.flip]
    · have he1 : e = 1 := by rw [he', if_neg h3]
      have hm : e ^ m = 1 := by rw [he1]; simp
      simp only [h3, and_false, if_false, hm]
      cases s <;> simp [signU, Sign.toInt]

/-- **The factor weights agree over $\mathbb Q$:** for $q = p$ and $e = \chi(-1) = (-1)^{(p-1)/2}$ (that is, $-1$ iff
$p \equiv 3 \bmod 4$), $M_p(d,\varepsilon)$ of `RatOdd.Mw` (Conway–Sloane's species factor) equals $M_q(d,\varepsilon)$. -/
theorem Mw_eq_Mq (p : ℕ) (e : ℤˣ) (he : (e : ℤ) = if p % 4 = 3 then -1 else 1) (d : ℕ) (s : Sign) :
    Mw p d s = Mq p e d s := by
  unfold Mw Mq Pq oddSpecies Species.diagFactor
  by_cases h0 : d = 0
  · subst h0; simp
  · by_cases ho : d % 2 = 1
    · have hodd : Odd d := Nat.odd_iff.2 ho
      simp [h0, ho, hodd, lowerProd]
    · have hev : ¬ Odd d := fun h => ho (Nat.odd_iff.1 h)
      simp [h0, ho, hev, lowerProd]
      have h4 : (d % 4 = 2) = (d / 2 % 2 = 1) := by
        apply propext; omega
      have hs := sign_aux p e he (d / 2) s
      simp only [h4]
      have hs' : (((if d / 2 % 2 = 1 ∧ p % 4 = 3 then s.flip else s).toInt : ℤ) : ℝ) =
          (((e : ℤ) : ℝ) ^ (d / 2) * (((signU s : ℤˣ) : ℤ) : ℝ)) := by
        rw [hs]; push_cast; ring
      rw [hs']
      ring

/-- **Over $\mathbb Q$ the paper's $\mathfrak p$-mass is Conway–Sloane's $p$-mass:** for a prime $p$ (any $p \ge 2$ works
formally), $e = \chi(-1)$ (i.e. $-1$ iff $p \equiv 3 \bmod 4$), an odd symbol $\sigma$ and a cutoff $N$,
`pMassNF p e σ N = pMassOdd p σ N` (`pMassOdd` is formula (3) of `conwaysloane1988`, proved equal to the §12 mass by
`pMassFormulaOdd`). -/
@[kb "hanke2011structure" "Lemma 7.3, p. 29 (F = Q: m_p = CS (3))"]
theorem pMassNF_eq_pMassOdd (p : ℕ) (e : ℤˣ) (he : (e : ℤ) = if p % 4 = 3 then -1 else 1) (σ : OddSymbol)
    (N : ℕ) : pMassNF p e σ N = pMassOdd p σ N := by
  unfold pMassNF pMassOdd
  rw [Rat.cast_prod]
  congr 1
  exact Finset.prod_congr rfl fun k _ => (Mw_eq_Mq p e he (σ k).dim (σ k).sign).symm

section NF

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

local notation "𝔬" => v.adicCompletionIntegers F

/-- **Paper 6, Lemma 7.3 and Remark 7.4 at $\mathfrak p \nmid 2$, every rank $n$:** for $z : \mathrm{Fin}\,n \to \mathbb N$
(the exponents $z_i$ of $\pi^{z_i}$, $\pi$ a uniformizer), $x : \mathrm{Fin}\,n \to \{\pm1\}$ (the square-class signs),
$c \in \mathcal O_{\mathfrak p}^\times$ a nonsquare unit ($\chi(c) = -1$), $q = |\mathcal O_F/\mathfrak p|$,
$e = \chi(-1)$, $N$ with $z_i < N$ for all $i$, and $\nu = \sum_i z_i = \operatorname{ord}_{\mathfrak p}\det_H$:
$$\beta(G)^{-1} = 2\,m_{\mathfrak p}(G)\,q^{-(n+1)\nu/2},\quad G = D(z,x),$$
where $m_{\mathfrak p}(G) = $ `pMassNF q e (symC z x) N` is Conway–Sloane's (3) with $p \to q$. -/
@[kb "hanke2011structure" "Lemma 7.3 and Remark 7.4, p. 29 (p ∤ 2, every number field, every rank n)"]
theorem invBeta_genND_eq_pMassNF (hv : (2 : 𝓞 F) ∉ v.asIdeal) {c : 𝔬} (hcU : IsUnit c) (hc : chiR c = -1)
    {n : ℕ} (z : Fin n → ℕ) (x : Fin n → ℤˣ) (N : ℕ) (hz : ∀ i, z i < N) :
    ((genND v c z x).beta)⁻¹ =
      2 * pMassNF (DVR.q 𝔬) (sgn 𝔬 (-1 : 𝔬)) (symC z x) N *
        ((DVR.q 𝔬 : ℝ) ^ (-((((∑ i, z i : ℕ) : ℝ) * ((n : ℝ) + 1)) / 2))) := by
  have hq : 0 < DVR.q 𝔬 := DVR.q_pos
  have hq0 : (0 : ℝ) < (DVR.q 𝔬 : ℝ) := by exact_mod_cast hq
  have hm := wtC_mul_pow_q (DVR.q 𝔬) hq (sgn 𝔬 (-1 : 𝔬)) (trivFrom_symC (z := z) (x := x) hz)
  rw [rkC_symC, zsC_symC] at hm
  rw [beta_genND hv hcU hc z x, inv_inv, ← hm]
  have hpow : Real.sqrt (DVR.q 𝔬 : ℝ) ^ ((n + 1) * ∑ i, z i) =
      (DVR.q 𝔬 : ℝ) ^ ((((∑ i, z i : ℕ) : ℝ) * ((n : ℝ) + 1)) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le]
    congr 1
    push_cast; ring
  rw [hpow, Real.rpow_neg hq0.le]
  have : (0 : ℝ) < (DVR.q 𝔬 : ℝ) ^ ((((∑ i, z i : ℕ) : ℝ) * ((n : ℝ) + 1)) / 2) := Real.rpow_pos_of_pos hq0 _
  field_simp

/-- **Paper 6, Lemma 7.3 at $\mathfrak p \nmid 2$ (binary case $n = 2$, paper's form):**
$\beta(G)^{-1} = 2\,m_{\mathfrak p}(G)\,q^{-3\nu/2}$, $\nu = z_0 + z_1$, $G = D(z,x)$ (here
$\operatorname{ord}_{\mathfrak p}(2) = 0$). -/
@[kb "hanke2011structure" "Lemma 7.3, p. 29 (n = 2, p ∤ 2, every number field)"]
theorem lemma_7_3_nf_odd (hv : (2 : 𝓞 F) ∉ v.asIdeal) {c : 𝔬} (hcU : IsUnit c) (hc : chiR c = -1)
    (z : Fin 2 → ℕ) (x : Fin 2 → ℤˣ) (N : ℕ) (hz : ∀ i, z i < N) :
    ((genND v c z x).beta)⁻¹ =
      2 * pMassNF (DVR.q 𝔬) (sgn 𝔬 (-1 : 𝔬)) (symC z x) N *
        ((DVR.q 𝔬 : ℝ) ^ (-((((z 0 + z 1 : ℕ) : ℝ) * 3) / 2))) := by
  rw [invBeta_genND_eq_pMassNF hv hcU hc z x N hz, Fin.sum_univ_two]
  norm_num

/-- **Lemma 7.3 / Remark 7.4 for an arbitrary nondegenerate local genus $G$ at $\mathfrak p \nmid 2$:** there are
$z, x$ with $G = D(z,x)$ (`exists_genND`) and $\beta(G)^{-1} = 2\,m_{\mathfrak p}(\mathrm{symbol}(z,x))\,q^{-(n+1)\nu/2}$,
$\nu = \sum_i z_i$, for every cutoff $N > \max z_i$. -/
@[kb "hanke2011structure" "Lemma 7.3 and Remark 7.4, p. 29 (every nondegenerate local genus, p ∤ 2)"]
theorem invBeta_eq_pMassNF_of_genus (hv : (2 : 𝓞 F) ∉ v.asIdeal) {c : 𝔬} (hcU : IsUnit c) (hc : chiR c = -1)
    {n : ℕ} (G : LocGenus v n) (hG : G.Nondeg) :
    ∃ (z : Fin n → ℕ) (x : Fin n → ℤˣ), G = genND v c z x ∧ ∀ N, (∀ i, z i < N) →
      (G.beta)⁻¹ = 2 * pMassNF (DVR.q 𝔬) (sgn 𝔬 (-1 : 𝔬)) (symC z x) N *
        ((DVR.q 𝔬 : ℝ) ^ (-((((∑ i, z i : ℕ) : ℝ) * ((n : ℝ) + 1)) / 2))) := by
  obtain ⟨z, x, rfl⟩ := exists_genND hv hcU hc G hG
  exact ⟨z, x, rfl, fun N hz => invBeta_genND_eq_pMassNF hv hcU hc z x N hz⟩

end NF

end

end QuadFormsKB.Hanke2011Structure.Lemma73NF

#print axioms QuadFormsKB.Hanke2011Structure.Lemma73NF.invBeta_genND_eq_pMassNF
#print axioms QuadFormsKB.Hanke2011Structure.Lemma73NF.lemma_7_3_nf_odd
#print axioms QuadFormsKB.Hanke2011Structure.Lemma73NF.invBeta_eq_pMassNF_of_genus
#print axioms QuadFormsKB.Hanke2011Structure.Lemma73NF.pMassNF_eq_pMassOdd
