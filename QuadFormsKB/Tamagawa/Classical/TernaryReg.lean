/-
# Classical special cases over $\mathbb Q$: the ternary character and $L(1,\chi)$

**Layer:** $\mathbb Q$.

For a ternary form $Q$ over $\mathbb Z$ and $m\in\mathbb Z$, the ternary character `chiTern (up Q) m` is
$\chi(p) = \left(\frac{-2\det H_Q\cdot m}{p}\right)$ at the odd primes $p\nmid\det H_Q$ and $0$ at $p = 2$. When it agrees with
the Kronecker character $\chi_D$ at every odd prime, its value at $s = 1$ is
$$L(1,\chi) = L(1,\chi_D)\Bigl(1 - \frac{\chi_D(2)}{2}\Bigr)$$
(`lOne_chiTern_eq`): the Euler factor at $2$ is removed.

**Proves** `charNF_intCast_eq_legendreSym'` (every integer, including multiples of $p$), `chiTern_up_odd`,
`chiTern_up_two`, `lOne_chiTern_eq`, and the identification for $x_0^2+x_1^2+x_2^2$ with $D$ = `gaussDisc m`
(`chiTern_sumSq_odd`) and for $x_0^2+x_1^2-x_2^2$ with $D$ = `realDisc m` (`chiTern_qInd_odd`).
-/
import QuadFormsKB.Tamagawa.Classical.Basic

open NumberField IsDedekindDomain

namespace QuadFormsKB.Tamagawa.Classical

open QuadFormsKB.Binary QuadFormsKB.Tamagawa.BinaryTauRat QuadFormsKB.Tamagawa.RatHeadline3 RatBridge RegProd
  QuadFormsKB.NFEuler

local notation "natGen" => Rat.HeightOneSpectrum.natGenerator

/-- **The residue symbol over $\mathcal O_{\mathbb Q}$ is the Legendre symbol, for every integer** $x$ (both sides vanish when
$p\mid x$). -/
theorem charNF_intCast_eq_legendreSym' (w : HeightOneSpectrum (𝓞 ℚ)) [Fact (natGen w).Prime] (x : ℤ) :
    Siegel.charNF w (x : 𝓞 ℚ) = legendreSym (natGen w) x := by
  by_cases hx : (natGen w : ℤ) ∣ x
  · have hxI : (x : 𝓞 ℚ) ∈ w.asIdeal := (intCast_mem_iff w x).mpr hx
    have hres : IsLocalRing.residue _ (LocalDensity.NF.ι w (x : 𝓞 ℚ)) = 0 := by
      rw [LocalDensity.DVR.residue_eq_zero_iff_dvd (LocalDensity.NF.irreducible_π w),
        LocalDensity.NF.π_dvd_ι_iff]
      exact hxI
    rw [Siegel.charNF, hres, quadraticChar_zero, eq_comm, legendreSym.eq_zero_iff]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd x _).mpr hx
  · exact charNF_intCast_eq_legendreSym w hx

/-- **`chiTern` at an odd prime** not dividing $\det H_Q$: the Legendre symbol of $-2\det H_Q\cdot m$. -/
theorem chiTern_up_odd (Q : QuadForm ℤ 3) (m : ℤ) (v : HeightOneSpectrum (𝓞 ℚ)) [Fact (natGen v).Prime]
    (hp2 : natGen v ≠ 2)
    (hdet : ¬ (natGen v : ℤ) ∣ Q.hessian.det) :
    chiTern (up Q) (m : 𝓞 ℚ) v = (legendreSym (natGen v) (-(2 * Q.hessian.det * m)) : ℝ) := by
  have h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal := by
    intro h
    have h' := (intCast_mem_iff v 2).mp (by exact_mod_cast h)
    have := (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) Nat.prime_two).mp
      (by exact_mod_cast h')
    exact hp2 this
  have hd : (up Q).hessian.det ∉ v.asIdeal := by
    rw [hessian_det_up3]; exact (intCast_mem_iff v _).not.mpr hdet
  have hG : Siegel.IsGoodPrimeNF (up Q) v := ⟨h2, hd⟩
  have hδ : (-1 : 𝓞 ℚ) ^ ((3 - 1) / 2) * (2 * (up Q).hessian.det) * (m : 𝓞 ℚ) =
      ((-(2 * Q.hessian.det * m) : ℤ) : 𝓞 ℚ) := by
    rw [hessian_det_up3]; push_cast; ring
  simp only [chiTern, Siegel.psiNF, hG, ↓reduceIte]
  rw [hδ, charNF_intCast_eq_legendreSym']

/-- **`chiTern` vanishes at $2$** ($2$ is a bad prime). -/
theorem chiTern_up_two (Q : QuadForm ℤ 3) (m : ℤ) (v : HeightOneSpectrum (𝓞 ℚ)) (hp2 : natGen v = 2) :
    chiTern (up Q) (m : 𝓞 ℚ) v = 0 := by
  have h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal := by
    have := (intCast_mem_iff v 2).mpr (by rw [hp2]; norm_num)
    exact_mod_cast this
  have hG : ¬ Siegel.IsGoodPrimeNF (up Q) v := fun h => h.1 h2
  simp only [chiTern, Siegel.psiNF, hG, ↓reduceIte]

/-- The prime of $\mathcal O_{\mathbb Q}$ above $2$. -/
theorem exists_natGen_eq_two : ∃ v : HeightOneSpectrum (𝓞 ℚ), natGen v = 2 := by
  obtain ⟨v, hv⟩ := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).surjective ⟨2, Nat.prime_two⟩
  exact ⟨v, congrArg Subtype.val hv⟩

/-- **$L(1,\chi)$ for a character that is $\chi_D$ at the odd primes and $0$ at $2$:**
$L(1,\chi) = L(1,\chi_D)\,(1-\chi_D(2)/2)$. -/
theorem lOne_eq_of_odd {χ : HeightOneSpectrum (𝓞 ℚ) → ℝ} (hχ : ∀ v, |χ v| ≤ 1) {D : ℤ} [IsQuadDisc D]
    (hodd : ∀ v, natGen v ≠ 2 → χ v = kronChi D v) (h2 : ∀ v, natGen v = 2 → χ v = 0) :
    LOne χ = Binary.LOne D * (1 - kronR D 2 / 2) := by
  obtain ⟨v₂, hv₂⟩ := exists_natGen_eq_two
  have hS : ∀ v ∉ ({v₂} : Finset _), χ v = kronChi D v := by
    intro v hv
    refine hodd v fun h => hv ?_
    rw [Finset.mem_singleton]
    exact (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective (Subtype.ext (show natGen v = natGen v₂ by rw [h, hv₂]))
  have hL := (hasLOne_kronChi (D := D)).congr_finite hχ (fun v => abs_kronChi_le v) {v₂} hS
  rw [hL.lOne_eq, Finset.prod_singleton]
  have hN : ((normP v₂ : ℕ) : ℝ) = 2 := by rw [normP_rat, hv₂]; norm_num
  simp only [lFactor, h2 v₂ hv₂, zero_mul, sub_zero, inv_one, kronChi, hv₂, hN, Real.rpow_neg_one]
  rw [one_div, inv_inv]
  ring

/-- **`lOne_eq_of_odd` for `chiTern`.** -/
theorem lOne_chiTern_eq (Q : QuadForm ℤ 3) (m : ℤ) {D : ℤ} [IsQuadDisc D]
    (hodd : ∀ v, natGen v ≠ 2 → chiTern (up Q) (m : 𝓞 ℚ) v = kronChi D v) :
    LOne (chiTern (up Q) (m : 𝓞 ℚ)) = Binary.LOne D * (1 - kronR D 2 / 2) :=
  lOne_eq_of_odd (fun v => abs_chiTern_le v _ _) hodd fun v hv => chiTern_up_two Q m v hv

/-- $\det H = 8$ for $x_0^2+x_1^2+x_2^2$. -/
theorem hessian_det_sumSq_three : (Siegel.sumSq 3).hessian.det = 8 := by
  simp [Siegel.sumSq, QuadForm.hessian, QuadForm.diag, Matrix.det_fin_three]

/-- $\det H = -8$ for $x_0^2+x_1^2-x_2^2$. -/
theorem hessian_det_qInd : qInd.hessian.det = -8 := by
  simp [qInd, QuadForm.hessian, QuadForm.diag, Fin.prod_univ_three]

theorem legendreSym_mul_four (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (a : ℤ) :
    legendreSym p (4 * a) = legendreSym p a := by
  have h2 : ((2 : ℤ) : ZMod p) ≠ 0 := by
    intro h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    have := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp (by exact_mod_cast h)
    exact hp2 this
  rw [show (4 : ℤ) * a = 2 ^ 2 * a by ring, legendreSym.mul, legendreSym.sq_one' p h2, one_mul]

/-- **The ternary character of $x_0^2+x_1^2+x_2^2$ at $m$ is $\chi_D$ at the odd primes**, $D$ = `gaussDisc m`
(the square class of $-2\det H\cdot m = -16m$ is that of $-m$). -/
theorem chiTern_sumSq_odd (m : ℤ) {D : ℤ} [IsQuadDisc D] (hD : D = gaussDisc m) (v : HeightOneSpectrum (𝓞 ℚ))
    (hp2 : natGen v ≠ 2) : chiTern (up (Siegel.sumSq 3)) (m : 𝓞 ℚ) v = kronChi D v := by
  have : Fact (natGen v).Prime := ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
  have hdet : ¬ (natGen v : ℤ) ∣ (Siegel.sumSq 3).hessian.det := by
    rw [hessian_det_sumSq_three, show (8 : ℤ) = 2 ^ 3 by norm_num]
    intro h
    have := Int.Prime.dvd_pow' (Nat.prime_iff_prime_int.mp (Fact.out : (natGen v).Prime) |> fun h => by
      exact_mod_cast (Fact.out : (natGen v).Prime)) h
    have := (Nat.prime_dvd_prime_iff_eq (Fact.out : (natGen v).Prime) Nat.prime_two).mp (by exact_mod_cast this)
    exact hp2 this
  rw [chiTern_up_odd _ _ _ hp2 hdet, kronChi, kronR, kronZ_odd_prime _ hp2, hessian_det_sumSq_three, hD, gaussDisc]
  have e : -(2 * 8 * m) = 4 * (4 * -m) := by ring
  rw [e, legendreSym_mul_four _ hp2, legendreSym_mul_four _ hp2]
  split_ifs
  · rfl
  · rw [show -4 * m = 4 * -m by ring, legendreSym_mul_four _ hp2]

/-- **The ternary character of $x_0^2+x_1^2-x_2^2$ at $m$ is $\chi_D$ at the odd primes**, $D$ = `realDisc m`
(the square class of $-2\det H\cdot m = 16m$ is that of $m$). -/
theorem chiTern_qInd_odd (m : ℤ) {D : ℤ} [IsQuadDisc D] (hD : D = realDisc m) (v : HeightOneSpectrum (𝓞 ℚ))
    (hp2 : natGen v ≠ 2) : chiTern (up qInd) (m : 𝓞 ℚ) v = kronChi D v := by
  have : Fact (natGen v).Prime := ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
  have hdet : ¬ (natGen v : ℤ) ∣ qInd.hessian.det := by
    rw [hessian_det_qInd, Int.dvd_neg, show (8 : ℤ) = 2 ^ 3 by norm_num]
    intro h
    have := Int.Prime.dvd_pow' (by exact_mod_cast (Fact.out : (natGen v).Prime)) h
    have := (Nat.prime_dvd_prime_iff_eq (Fact.out : (natGen v).Prime) Nat.prime_two).mp (by exact_mod_cast this)
    exact hp2 this
  rw [chiTern_up_odd _ _ _ hp2 hdet, kronChi, kronR, kronZ_odd_prime _ hp2, hessian_det_qInd, hD, realDisc]
  have e : -(2 * -8 * m) = 4 * (4 * m) := by ring
  rw [e, legendreSym_mul_four _ hp2, legendreSym_mul_four _ hp2]
  split_ifs
  · rfl
  · rw [legendreSym_mul_four _ hp2]

end QuadFormsKB.Tamagawa.Classical
