import QuadFormsKB.Historical.Gauss.PeriodsQuadratic

/-!
# The leading terms of $Y$ and $Z$ in $4\Phi_p = Y^2 \mp p Z^2$ (Disquisitiones Arithmeticae, Art. 357)

the historical sources (Gauss, *Disq. Arith.* Art. 357; promised in Art. 124).

`gauss_cyclotomic_decomposition` (in `PeriodsQuadratic.lean`) gives $Y, Z \in \mathbb{Z}[X]$ and $s$ with
$2z = Y + sZ$, $2z' = Y - sZ$, $4\Phi_p = Y^2 - p^* Z^2$, but does not pin down the degrees and leading terms.
This file proves, unconditionally, the strengthened statement with Gauss's leading terms
($m = (p-1)/2$): $Y = 2X^m + X^{m-1} + \dots$ and $Z = X^{m-1} + \dots$.

* `gauss_cyclotomic_decomposition_leading`: the conclusions of `gauss_cyclotomic_decomposition` together with
  $\deg Y = m$, $[X^m]Y = 2$, $[X^{m-1}]Y = 1$, $\deg Z = m-1$, $[X^{m-1}]Z = 1$.
* `gauss_four_cyclotomic_leading`: the integral identity $4\Phi_p = Y^2 - p^* Z^2$ with these leading terms and
  no field in the statement.

Route: $z, z'$ are monic of degree $m$ and their next coefficients are $-\eta_0$, $-\eta_1$ (minus the sums of the
roots, which are the two Gaussian periods); $\eta_0 + \eta_1 = -1$ and $(\eta_0 - \eta_1)^2 = p^* = s^2$.
From $2z = Y + sZ$, $2z' = Y - sZ$ one gets $Y = z + z'$ and $sZ = z - z'$ (characteristic zero), and the
coefficients are read off. If the coefficient of $Z$ comes out as $-1$, replace $(s, Z)$ by $(-s, -Z)$.
-/

namespace QuadFormsKB.Historical.Gauss

open scoped Classical
open Polynomial

section Leading

variable {K : Type*} [Field K] [CharZero K] {p : ℕ} [Fact p.Prime]

/-- Coefficient bookkeeping: from $2z = Y + sZ$, $2z' = Y - sZ$ with $z, z'$ monic of degree $N$ and next
coefficients $-\eta_0, -\eta_1$ ($\eta_0 + \eta_1 = -1$, $(\eta_0 - \eta_1)^2 = s^2 \ne 0$), read off the
leading terms of $Y$ and $Z$. -/
private theorem leading_aux {N : ℕ} (hN : 1 ≤ N) {z z' : K[X]} (hz : z.Monic) (hz' : z'.Monic)
    (dz : z.natDegree = N) (dz' : z'.natDegree = N) {η0 η1 s : K}
    (nz : z.coeff (N - 1) = -η0) (nz' : z'.coeff (N - 1) = -η1) (hsum : η0 + η1 = -1)
    (hg0 : η0 - η1 ≠ 0) (hgs : (η0 - η1) ^ 2 = s ^ 2) {Y Z : ℤ[X]}
    (e0 : 2 * z = Y.map (Int.castRingHom K) + C s * Z.map (Int.castRingHom K))
    (e1 : 2 * z' = Y.map (Int.castRingHom K) - C s * Z.map (Int.castRingHom K)) :
    Y.natDegree = N ∧ Y.coeff N = 2 ∧ Y.coeff (N - 1) = 1 ∧ Z.natDegree = N - 1 ∧
      ((Z.coeff (N - 1) = 1 ∧ s = -(η0 - η1)) ∨ (Z.coeff (N - 1) = -1 ∧ s = η0 - η1)) := by
  have hY : Y.map (Int.castRingHom K) = z + z' := by
    have h : (2 : K[X]) * Y.map (Int.castRingHom K) = 2 * (z + z') := by
      linear_combination (-1 : K[X]) * e0 - e1
    exact mul_left_cancel₀ two_ne_zero h
  have hZ : C s * Z.map (Int.castRingHom K) = z - z' := by
    have h : (2 : K[X]) * (C s * Z.map (Int.castRingHom K)) = 2 * (z - z') := by
      linear_combination (-1 : K[X]) * e0 + e1
    exact mul_left_cancel₀ two_ne_zero h
  have hzc : z.coeff N = 1 := by
    have := hz.coeff_natDegree
    rwa [dz] at this
  have hzc' : z'.coeff N = 1 := by
    have := hz'.coeff_natDegree
    rwa [dz'] at this
  have hzhigh : ∀ i, N < i → z.coeff i = 0 := fun i hi =>
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hzhigh' : ∀ i, N < i → z'.coeff i = 0 := fun i hi =>
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hYc : ∀ i, (Y.coeff i : K) = z.coeff i + z'.coeff i := by
    intro i
    have := congrArg (fun q => q.coeff i) hY
    simpa [coeff_map] using this
  have hZc : ∀ i, s * (Z.coeff i : K) = z.coeff i - z'.coeff i := by
    intro i
    have := congrArg (fun q => q.coeff i) hZ
    simpa [coeff_map, coeff_C_mul] using this
  have hs0 : s ≠ 0 := by
    intro h
    have h2 : (η0 - η1) ^ 2 = 0 := by rw [hgs, h]; ring
    exact hg0 ((pow_eq_zero_iff two_ne_zero).mp h2)
  have hY2 : Y.coeff N = 2 := by
    have : (Y.coeff N : K) = 2 := by rw [hYc, hzc, hzc']; norm_num
    exact_mod_cast this
  have hY1 : Y.coeff (N - 1) = 1 := by
    have : (Y.coeff (N - 1) : K) = 1 := by
      rw [hYc, nz, nz']; linear_combination (-1 : K) * hsum
    exact_mod_cast this
  have hYhigh : ∀ i, N < i → Y.coeff i = 0 := by
    intro i hi
    have : (Y.coeff i : K) = 0 := by rw [hYc, hzhigh i hi, hzhigh' i hi]; simp
    exact_mod_cast this
  have hYdeg : Y.natDegree = N :=
    natDegree_eq_of_le_of_coeff_ne_zero (natDegree_le_iff_coeff_eq_zero.mpr hYhigh)
      (by rw [hY2]; norm_num)
  have hZhigh : ∀ i, N ≤ i → Z.coeff i = 0 := by
    intro i hi
    have hd : z.coeff i - z'.coeff i = 0 := by
      rcases hi.eq_or_lt with h | h
      · rw [← h, hzc, hzc']; ring
      · rw [hzhigh i h, hzhigh' i h]; ring
    have h0 : s * (Z.coeff i : K) = 0 := by rw [hZc, hd]
    have : (Z.coeff i : K) = 0 := (mul_eq_zero.mp h0).resolve_left hs0
    exact_mod_cast this
  have hle : Z.natDegree ≤ N - 1 :=
    natDegree_le_iff_coeff_eq_zero.mpr (fun i hi => hZhigh i (by omega))
  have hm : s * (Z.coeff (N - 1) : K) = -(η0 - η1) := by
    rw [hZc, nz, nz']; ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hgs with h | h
  · have hc : (Z.coeff (N - 1) : K) = -1 :=
      mul_left_cancel₀ hs0 (by linear_combination hm - h)
    have hc' : Z.coeff (N - 1) = -1 := by exact_mod_cast hc
    refine ⟨hYdeg, hY2, hY1, natDegree_eq_of_le_of_coeff_ne_zero hle (by rw [hc']; norm_num),
      Or.inr ⟨hc', h.symm⟩⟩
  · have hc : (Z.coeff (N - 1) : K) = 1 :=
      mul_left_cancel₀ hs0 (by linear_combination hm - h)
    have hc' : Z.coeff (N - 1) = 1 := by exact_mod_cast hc
    refine ⟨hYdeg, hY2, hY1, natDegree_eq_of_le_of_coeff_ne_zero hle (by rw [hc']; norm_num),
      Or.inl ⟨hc', by linear_combination h⟩⟩

/-- **Gauss's decomposition of the cyclotomic polynomial, with leading terms** (the historical sources,
*Disq. Arith.* Art. 357, promised in Art. 124). Let $p$ be an odd prime, $\zeta$ a primitive $p$-th root of unity
in a field $K$ of characteristic zero, $z = \prod_{a \text{ residue}} (X - \zeta^a)$ and
$z' = \prod_{a \text{ nonresidue}} (X - \zeta^a)$. Then there are $Y, Z \in \mathbb{Z}[X]$ and $s \in K$ with
$s^2 = p^* = (-1)^{(p-1)/2} p$, $2z = Y + sZ$, $2z' = Y - sZ$, $4\Phi_p = Y^2 - p^* Z^2$ (all as in
`gauss_cyclotomic_decomposition`), and with $m = (p-1)/2$: $\deg Y = m$, $Y = 2X^m + X^{m-1} + \dots$
(coefficient of $X^m$ is $2$, of $X^{m-1}$ is $1$), and $\deg Z = m - 1$ with coefficient of $X^{m-1}$ equal to $1$.
Unconditional. For $p = 3$ ($m = 1$): $Y = 2X + 1$, $Z = 1$. Exponents are as in Gauss (no index shift is
involved). The pair $(Y, Z)$ is unique up to the sign of $(s, Z)$, and the normalisation $[X^{m-1}] Z = 1$
fixes the sign of $s$ (it is $-(\eta_0 - \eta_1)$ or $+(\eta_0 - \eta_1)$ depending on the choice made in the
proof). Nothing differs from the historical sources statement. -/
@[kb "gauss1801" "Art. 357"]
theorem gauss_cyclotomic_decomposition_leading (hp : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    ∃ (Y Z : ℤ[X]) (s : K),
      s ^ 2 = (((-1) ^ ((p - 1) / 2) * p : ℤ) : K) ∧
      2 * (∏ u ∈ Finset.univ.filter (fun u : (ZMod p)ˣ => IsSquare u),
            (X - C (ζ ^ (u : ZMod p).val)))
        = Y.map (Int.castRingHom K) + C s * Z.map (Int.castRingHom K) ∧
      2 * (∏ u ∈ Finset.univ.filter (fun u : (ZMod p)ˣ => ¬ IsSquare u),
            (X - C (ζ ^ (u : ZMod p).val)))
        = Y.map (Int.castRingHom K) - C s * Z.map (Int.castRingHom K) ∧
      4 * cyclotomic p ℤ = Y ^ 2 - C (((-1) ^ ((p - 1) / 2) * p : ℤ)) * Z ^ 2 ∧
      Y.natDegree = (p - 1) / 2 ∧ Y.coeff ((p - 1) / 2) = 2 ∧ Y.coeff ((p - 1) / 2 - 1) = 1 ∧
      Z.natDegree = (p - 1) / 2 - 1 ∧ Z.coeff ((p - 1) / 2 - 1) = 1 := by
  obtain ⟨a, ha⟩ := exists_nonsquare_unit hp
  obtain ⟨Y, Z, s, hs2, e0, e1, h4⟩ := gauss_cyclotomic_decomposition hp hζ
  have hzf : ∏ u ∈ Finset.univ.filter (fun u : (ZMod p)ˣ => IsSquare u),
        (X - C (ζ ^ (u : ZMod p).val))
      = ∏ h : squaresSubgroup p, (X - C (rootPow ζ (((h : (ZMod p)ˣ)) : ZMod p))) :=
    prod_filter_isSquare (fun u : (ZMod p)ˣ => X - C (rootPow ζ (u : ZMod p)))
  have hzf' : ∏ u ∈ Finset.univ.filter (fun u : (ZMod p)ˣ => ¬ IsSquare u),
        (X - C (ζ ^ (u : ZMod p).val))
      = ∏ h : squaresSubgroup p,
          (X - C (rootPow ζ (((a * (h : (ZMod p)ˣ) : (ZMod p)ˣ)) : ZMod p))) :=
    prod_filter_not_isSquare (fun u : (ZMod p)ˣ => X - C (rootPow ζ (u : ZMod p))) ha
  have e0r := e0
  have e1r := e1
  rw [hzf] at e0r
  rw [hzf'] at e1r
  set z : K[X] := ∏ h : squaresSubgroup p, (X - C (rootPow ζ (((h : (ZMod p)ˣ)) : ZMod p)))
    with hzdef
  set z' : K[X] := ∏ h : squaresSubgroup p,
      (X - C (rootPow ζ (((a * (h : (ZMod p)ˣ) : (ZMod p)ˣ)) : ZMod p))) with hzdef'
  have hzm : z.Monic := monic_prod_of_monic _ _ fun h _ => monic_X_sub_C _
  have hzm' : z'.Monic := monic_prod_of_monic _ _ fun h _ => monic_X_sub_C _
  have hzd : z.natDegree = Fintype.card (squaresSubgroup p) := by
    rw [hzdef, natDegree_prod_of_monic _ _ (fun h _ => monic_X_sub_C _)]
    simp
  have hzd' : z'.natDegree = Fintype.card (squaresSubgroup p) := by
    rw [hzdef', natDegree_prod_of_monic _ _ (fun h _ => monic_X_sub_C _)]
    simp
  have hzz : z * z' = cyclotomic p K := by
    rw [← prod_units_eq_cyclotomic hζ]
    exact (prod_units_split (p := p) (fun u : (ZMod p)ˣ => X - C (rootPow ζ (u : ZMod p))) ha).symm
  have hdeg : z.natDegree + z'.natDegree = p - 1 := by
    rw [← hzm.natDegree_mul hzm', hzz, natDegree_cyclotomic, Nat.totient_prime Fact.out]
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hzN : z.natDegree = (p - 1) / 2 := by omega
  have hzN' : z'.natDegree = (p - 1) / 2 := by omega
  have hN : 1 ≤ (p - 1) / 2 := by omega
  have hnz : z.coeff ((p - 1) / 2 - 1) = -periodSum ζ (squaresSubgroup p) 1 := by
    have h : nextCoeff z = -∑ h : squaresSubgroup p, rootPow ζ (((h : (ZMod p)ˣ)) : ZMod p) :=
      prod_X_sub_C_nextCoeff _
    rw [nextCoeff_of_natDegree_pos (by omega), hzN] at h
    rw [h]
    simp [periodSum]
  have hnz' : z'.coeff ((p - 1) / 2 - 1) = -periodSum ζ (squaresSubgroup p) (a : ZMod p) := by
    have h : nextCoeff z' = -∑ h : squaresSubgroup p,
        rootPow ζ (((a * (h : (ZMod p)ˣ) : (ZMod p)ˣ)) : ZMod p) :=
      prod_X_sub_C_nextCoeff _
    rw [nextCoeff_of_natDegree_pos (by omega), hzN'] at h
    rw [h]
    simp [periodSum, Units.val_mul]
  have hsum := periodSum_squares_add hζ ha
  have hs := periodSum_squares_sub_sq hp hζ ha
  have hg0 : periodSum ζ (squaresSubgroup p) 1 - periodSum ζ (squaresSubgroup p) (a : ZMod p) ≠ 0 := by
    intro h
    rw [h] at hs
    have h0 : ((((-1) ^ ((p - 1) / 2) * p : ℤ)) : K) = 0 := by rw [← hs]; ring
    have h1 : (((-1) ^ ((p - 1) / 2) * p : ℤ)) = 0 := by exact_mod_cast h0
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact pow_ne_zero _ (by norm_num) h2
    · exact hp0 h2
  obtain ⟨hYd, hY2, hY1, hZd, hcases⟩ := leading_aux hN hzm hzm' hzN hzN' hnz hnz' hsum hg0
    (hs.trans hs2.symm) e0r e1r
  rcases hcases with ⟨hc, -⟩ | ⟨hc, -⟩
  · exact ⟨Y, Z, s, hs2, e0, e1, h4, hYd, hY2, hY1, hZd, hc⟩
  · refine ⟨Y, -Z, -s, by rw [neg_sq]; exact hs2, ?_, ?_, ?_, hYd, hY2, hY1, ?_, ?_⟩
    · rw [e0]; simp
    · rw [e1]; simp
    · rw [h4, neg_sq]
    · rw [natDegree_neg]; exact hZd
    · rw [coeff_neg, hc]; norm_num

/-- **The integral identity $4\Phi_p = Y^2 - p^* Z^2$ with Gauss's leading terms** (the historical sources,
*Disq. Arith.* Art. 357): for every odd prime $p$ and $m = (p-1)/2$ there are $Y, Z \in \mathbb{Z}[X]$ with
$4\Phi_p = Y^2 - (-1)^{(p-1)/2} p Z^2$, $\deg Y = m$, $Y = 2X^m + X^{m-1} + \dots$, $\deg Z = m-1$ and the
coefficient of $X^{m-1}$ in $Z$ equal to $1$. This is `gauss_cyclotomic_decomposition_leading` over
$\mathbb{C}$, with the field forgotten. Unconditional. -/
@[kb "gauss1801" "Art. 357"]
theorem gauss_four_cyclotomic_leading (hp : p ≠ 2) :
    ∃ Y Z : ℤ[X], 4 * cyclotomic p ℤ = Y ^ 2 - C (((-1) ^ ((p - 1) / 2) * p : ℤ)) * Z ^ 2 ∧
      Y.natDegree = (p - 1) / 2 ∧ Y.coeff ((p - 1) / 2) = 2 ∧ Y.coeff ((p - 1) / 2 - 1) = 1 ∧
      Z.natDegree = (p - 1) / 2 - 1 ∧ Z.coeff ((p - 1) / 2 - 1) = 1 := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨Y, Z, _, -, -, -, h, hY, hY2, hY1, hZ, hZ1⟩ :=
    gauss_cyclotomic_decomposition_leading (K := ℂ) hp (Complex.isPrimitiveRoot_exp p (NeZero.ne p))
  exact ⟨Y, Z, h, hY, hY2, hY1, hZ, hZ1⟩

end Leading

end QuadFormsKB.Historical.Gauss
