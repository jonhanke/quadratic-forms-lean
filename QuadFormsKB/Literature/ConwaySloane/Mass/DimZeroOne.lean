/-
# Conway–Sloane 1988, §6: the mass formula in dimensions 0 and 1, with Tamagawa factor 1

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), §6, p. 266 (bibliography key `conwaysloane1988`). Formula (2) reads
$$m(f) = 2\,\pi^{-n(n+1)/4}\prod_{j=1}^n\Gamma(j/2)\prod_p\bigl(2m_p(f)\bigr)\qquad(n \ge 2).$$
The paper explains that the initial factor $2$ is the Tamagawa number of $SO_n$ and "should therefore be replaced by 1
in dimensions 0 and 1, because then both the local and global forms of determinant $d$ are unique"; moreover in
dimension $0$ each factor $2m_p(f)$ is to be replaced by $1$ (§6, p. 266, the proper $p$-mass).

**Conventions.** A form of dimension $1$ is $\langle d\rangle$, Gram matrix `!![d]` ($f(x_0) = dx_0^2$), with quadratic form
`LocalDensity.ofMatrixZ !![d]`; a form of dimension $0$ is any `Q : QuadForm ℤ 0`. The mass is `Siegel.mass`
($\mathrm{GL}$-classes, improper automorphisms included). The $p$-masses $m_p$ are those of the symbols, as in the
working form of (2) elsewhere in the library: `pMassTwo τ N₂` for a 2-adic symbol $\tau$ of $\langle d\rangle$ and
`pMassOdd p (σ p) (N p)` for a $p$-adic symbol $\sigma_p$ ($p$ odd); by formula (3), proved at every prime
(`pMassFormulaOdd`, `pMassDensity_eq_pMassTwo`), these are the $p$-masses of §12. For $p \nmid 2d$ the $p$-mass is
$\mathrm{std}_p = \frac12$ in dimension $1$, so $2m_p = 1$ there (`two_mul_stdP_dim_one`) and the product over all
primes reduces to the product over $p \mid 2d$.

**Proves**
* `isTwoSymbolOf_dim_one`, `isOddSymbolOf_dim_one`: every 2-adic symbol of a one-dimensional form has a single
  constituent $\mathrm I_1$ with unit $u \in \{1,3,5,7\}$; every $p$-adic symbol has a single constituent of dimension $1$.
* `mass_dim_one` (§6, p. 266, dimension 1): for $d > 0$ and any local symbols of $\langle d\rangle$,
  $m(\langle d\rangle) = 1\cdot\pi^{-1/2}\Gamma(\frac12)\prod_{p \mid 2d}2m_p = \frac12$. Unconditional.
* `mass_dim_zero` (§6, p. 266, dimension 0): the mass of the zero-dimensional form is
  $1\cdot\pi^{0}\cdot(\text{empty product}) \cdot \prod_p 1 = 1$. Unconditional.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.DimOne
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicFinal
import QuadFormsKB.Siegel.RankOne

open Matrix QuadFormsKB QuadFormsKB.Siegel QuadFormsKB.Siegel.RankOne QuadFormsKB.LocalDensity Real

namespace QuadFormsKB.ConwaySloane.Mass

/-! ### The symbols of a one-dimensional form -/

/-- **Every 2-adic symbol of a one-dimensional form** is `singleTwo e ⟨1, (u/2), I, u⟩` for some $e \ge 0$ and
$u \in \{1, 3, 5, 7\}$: the decomposition has a single block $2^e u x^2$. -/
theorem isTwoSymbolOf_dim_one {F : Matrix (Fin 1) (Fin 1) ℚ_[2]} {τ : TwoSymbol} (h : IsTwoSymbolOf F τ) :
    ∃ e : ℕ, ∃ u : ℤ, (u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7) ∧
      τ = singleTwo e ⟨1, jacobiTwo u, .I, (u : ZMod 8)⟩ := by
  obtain ⟨D, hV, hE, hdim, -, rfl⟩ := h
  match D, hV, hE, hdim with
  | [], _, _, hdim => exact absurd hdim (by simp [Cassels.dyDim])
  | b :: D', hV, hE, hdim =>
    have hD' : D' = [] := by
      cases D' with
      | nil => rfl
      | cons b' D'' =>
        exfalso
        have h1 : 1 ≤ b.dim := by cases b <;> simp [Cassels.DyBlock.dim]
        have h2 : 1 ≤ b'.dim := by cases b' <;> simp [Cassels.DyBlock.dim]
        simp only [Cassels.dyDim] at hdim
        omega
    subst hD'
    cases b with
    | hyp e => simp [Cassels.dyDim, Cassels.DyBlock.dim] at hdim
    | ell e => simp [Cassels.dyDim, Cassels.DyBlock.dim] at hdim
    | sq e u =>
      have he : 0 ≤ e := hE _ (List.mem_singleton_self _)
      have hu : u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7 := hV _ (List.mem_singleton_self _)
      refine ⟨e.toNat, u, hu, ?_⟩
      funext k
      by_cases hk : k = e.toNat
      · subst hk
        simp [blockSymbol, singleTwo, blockExp, Int.toNat_of_nonneg he, Sign.prodList, IsSqBlock,
          blockOddity, Cassels.DyBlock.dim, Sign.mul, blockSign]
        cases jacobiTwo u <;> rfl
      · have hk' : ¬ e = (k : ℤ) := by omega
        simp [blockSymbol, singleTwo, blockExp, hk, hk', Sign.prodList, TwoFactor.trivial]

/-- **Every $p$-adic symbol of a one-dimensional form** ($p$ odd) is `singleOdd a ⟨1, ε⟩`. -/
theorem isOddSymbolOf_dim_one {p : ℕ} [Fact p.Prime] {F : Matrix (Fin 1) (Fin 1) ℚ_[p]} {σ : OddSymbol}
    (h : IsOddSymbolOf p F σ) : ∃ a : ℕ, ∃ ε : Sign, σ = singleOdd a ⟨1, ε⟩ := by
  classical
  obtain ⟨z, u, -, -, rfl⟩ := h
  refine ⟨z 0, if IsSquare (u 0) then .plus else .minus, ?_⟩
  funext k
  by_cases hk : z 0 = k
  · subst hk
    have hc : Fintype.card {i : Fin 1 // z i = z 0} = 1 :=
      Fintype.card_eq_one_iff.2 ⟨⟨0, rfl⟩, fun ⟨i, _⟩ => by simp [Fin.fin_one_eq_zero i]⟩
    have hp : (∏ i : {i : Fin 1 // z i = z 0}, u i) = u 0 := by
      rw [Fintype.prod_eq_single ⟨0, rfl⟩ (fun ⟨i, _⟩ hi => absurd (Subtype.ext (Fin.fin_one_eq_zero i)) hi)]
    simp only [oddSymbolOfDiag, singleOdd, ite_true, hc, hp]
  · have hk' : k ≠ z 0 := fun e => hk e.symm
    have hc : Fintype.card {i : Fin 1 // z i = k} = 0 :=
      Fintype.card_eq_zero_iff.2 ⟨fun ⟨i, hi⟩ => hk (by rwa [Fin.fin_one_eq_zero i] at hi)⟩
    have hp : (∏ i : {i : Fin 1 // z i = k}, u i) = 1 := by
      have : IsEmpty {i : Fin 1 // z i = k} := Fintype.card_eq_zero_iff.1 hc
      exact Finset.prod_of_isEmpty _
    simp only [oddSymbolOfDiag, singleOdd, hk', ite_false, hc, hp, IsSquare.one, ite_true, OddFactor.trivial]

/-! ### Dimension 1 -/

/-- In dimension 1 the standard $p$-mass is $\frac12$ at every prime, so $2\,\mathrm{std}_p = 1$: the primes $p \nmid 2d$
contribute the factor $1$ to $\prod_p 2m_p$. -/
theorem two_mul_stdP_dim_one (p : ℕ) (d : ℤ) : 2 * (stdP p 1 d : ℝ) = 1 := by
  simp [stdP, lowerProd]

theorem pMassTwo_dim_one {d : ℤ} {τ : TwoSymbol} {N₂ : ℕ}
    (hτ : IsTwoSymbolOf ((!![d] : Matrix (Fin 1) (Fin 1) ℤ).map (Int.cast : ℤ → ℚ_[2])) τ)
    (hτN : τ.SupportedBelow N₂) : pMassTwo τ N₂ = 1 / 4 := by
  obtain ⟨e, u, hu, rfl⟩ := isTwoSymbolOf_dim_one hτ
  have hoct : octane ⟨1, jacobiTwo u, .I, (u : ZMod 8)⟩ = 1 ∨ octane ⟨1, jacobiTwo u, .I, (u : ZMod 8)⟩ = 7 := by
    rcases hu with rfl | rfl | rfl | rfl <;> decide
  have hsupp : ∀ k, e + 1 ≤ k → singleTwo e ⟨1, jacobiTwo u, .I, (u : ZMod 8)⟩ k = TwoFactor.trivial := by
    intro k hk; simp [singleTwo]; omega
  rcases le_total (e + 1) N₂ with h | h
  · rw [pMassTwo_congr hsupp h]
    exact pMassTwo_single e _ rfl rfl hoct
  · rw [← pMassTwo_congr hτN h]
    exact pMassTwo_single e _ rfl rfl hoct

theorem pMassOdd_dim_one {p : ℕ} [Fact p.Prime] {d : ℤ} {σ : OddSymbol} {N : ℕ}
    (hσ : IsOddSymbolOf p ((!![d] : Matrix (Fin 1) (Fin 1) ℤ).map (Int.cast : ℤ → ℚ_[p])) σ)
    (hσN : ∀ k, N ≤ k → σ k = OddFactor.trivial) : pMassOdd p σ N = 1 / 2 := by
  obtain ⟨a, ε, rfl⟩ := isOddSymbolOf_dim_one hσ
  have hsupp : ∀ k, a + 1 ≤ k → singleOdd a ⟨1, ε⟩ k = OddFactor.trivial := by
    intro k hk; simp [singleOdd]; omega
  rcases le_total (a + 1) N with h | h
  · rw [pMassOdd_congr p hsupp h]
    exact pMassOdd_single p a ε
  · rw [← pMassOdd_congr p hσN h]
    exact pMassOdd_single p a ε

theorem ofMatrixZ_unary (d : ℤ) : ofMatrixZ (!![d] : Matrix (Fin 1) (Fin 1) ℤ) = unary d := by
  apply QuadForm.ext
  ext i j
  fin_cases i; fin_cases j
  simp [ofMatrixZ, unary, QuadForm.diag]

/-- **§6, the mass formula in dimension 1 with Tamagawa factor 1** (Conway–Sloane 1988, p. 266: the initial 2 of (2)
"should therefore be replaced by 1 in dimensions 0 and 1"). For $d > 0$, a 2-adic symbol $\tau$ of $\langle d\rangle$
supported below $N_2$ and $p$-adic symbols $\sigma_p$ of $\langle d\rangle$ supported below $N_p$ ($p \mid d$ odd),
$$m(\langle d\rangle) = 1\cdot\pi^{-1\cdot2/4}\prod_{j=1}^{1}\Gamma(j/2)\prod_{p \mid 2d}2m_p(\langle d\rangle) = \frac12.$$
(The primes $p \nmid 2d$ contribute $2\,\mathrm{std}_p = 1$, `two_mul_stdP_dim_one`.) Unconditional. -/
@[kb "conwaysloane1988" "§6, p. 266 (dimension 1, Tamagawa factor 1)"]
theorem mass_dim_one {d : ℤ} (hd : 0 < d) (τ : TwoSymbol) (N₂ : ℕ)
    (hτ : IsTwoSymbolOf ((!![d] : Matrix (Fin 1) (Fin 1) ℤ).map (Int.cast : ℤ → ℚ_[2])) τ)
    (hτN : τ.SupportedBelow N₂) (σ : ℕ → OddSymbol) (N : ℕ → ℕ)
    (hodd : ∀ p : ℕ, (hp : p.Prime) → p ≠ 2 → (p : ℤ) ∣ d →
      haveI : Fact p.Prime := ⟨hp⟩
      IsOddSymbolOf p ((!![d] : Matrix (Fin 1) (Fin 1) ℤ).map (Int.cast : ℤ → ℚ_[p])) (σ p) ∧
        ∀ k, N p ≤ k → σ p k = OddFactor.trivial) :
    Siegel.mass (ofMatrixZ (!![d] : Matrix (Fin 1) (Fin 1) ℤ)) =
        1 * π ^ (-((1 : ℝ) * (1 + 1)) / 4) * (∏ j ∈ Finset.Icc (1 : ℕ) 1, Real.Gamma ((j : ℝ) / 2)) *
          ∏ p ∈ (2 * d).natAbs.primeFactors,
            (2 * (if p = 2 then pMassTwo τ N₂ else pMassOdd p (σ p) (N p))) ∧
      Siegel.mass (ofMatrixZ (!![d] : Matrix (Fin 1) (Fin 1) ℤ)) = 1 / 2 := by
  have hm : Siegel.mass (ofMatrixZ (!![d] : Matrix (Fin 1) (Fin 1) ℤ)) = 1 / 2 := by
    rw [ofMatrixZ_unary]; exact mass_unary d
  refine ⟨?_, hm⟩
  have h2 : 2 ∈ (2 * d).natAbs.primeFactors := by
    rw [Nat.mem_primeFactors]
    refine ⟨Nat.prime_two, ?_, by simp; omega⟩
    rw [Int.natAbs_mul]; exact dvd_mul_right _ _
  have hprod : ∏ p ∈ (2 * d).natAbs.primeFactors,
      (2 * (if p = 2 then pMassTwo τ N₂ else pMassOdd p (σ p) (N p))) = 1 / 2 := by
    rw [← Finset.mul_prod_erase _ _ h2, if_pos rfl, pMassTwo_dim_one hτ hτN,
      Finset.prod_eq_one (fun p hp => by
        have hp2 : p ≠ 2 := Finset.ne_of_mem_erase hp
        have hpf := (Finset.mem_erase.1 hp).2
        rw [Nat.mem_primeFactors] at hpf
        obtain ⟨hpp, hpd, -⟩ := hpf
        have hpd' : (p : ℤ) ∣ d := by
          have h1 : (p : ℤ) ∣ 2 * d := Int.natCast_dvd.2 hpd
          rcases (Int.Prime.dvd_mul' hpp h1) with h | h
          · exfalso
            have : p ∣ 2 := by exact_mod_cast h
            exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 this)
          · exact h
        have : Fact p.Prime := ⟨hpp⟩
        obtain ⟨hs, hsN⟩ := hodd p hpp hp2 hpd'
        rw [if_neg hp2, pMassOdd_dim_one hs hsN]; norm_num)]
    norm_num
  rw [hprod, hm, Finset.Icc_self, Finset.prod_singleton, Nat.cast_one, Real.Gamma_one_half_eq]
  have : π ^ (-((1 : ℝ) * (1 + 1)) / 4) * √π = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add Real.pi_pos]; norm_num
  rw [one_mul, this]; norm_num

/-! ### Dimension 0 -/

theorem quadForm_zero_eq (Q Q' : QuadForm ℤ 0) : Q = Q' := by
  apply QuadForm.ext
  ext i
  exact Fin.elim0 i

theorem card_aut_dim_zero (Q : QuadForm ℤ 0) : Nat.card (Aut Q) = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => Subtype.ext (Units.ext (Matrix.ext fun i => Fin.elim0 i))⟩, ⟨1⟩⟩

/-- **§6, the mass formula in dimension 0** (Conway–Sloane 1988, p. 266: the initial 2 of (2) is replaced by 1, and
each factor $2m_p$ by 1 for the zero-dimensional form): the mass of the zero-dimensional form is
$1\cdot\pi^{-0\cdot1/4}\prod_{j=1}^{0}\Gamma(j/2) = 1$ (one class, trivial automorphism group). Unconditional. -/
@[kb "conwaysloane1988" "§6, p. 266 (dimension 0, Tamagawa factor 1)"]
theorem mass_dim_zero (Q : QuadForm ℤ 0) :
    Siegel.mass Q = 1 * π ^ (-((0 : ℝ) * (0 + 1)) / 4) * ∏ j ∈ Finset.Icc (1 : ℕ) 0, Real.Gamma ((j : ℝ) / 2) ∧
      Siegel.mass Q = 1 := by
  have hcl : genusClasses Q = {classOf Q} := by
    ext c
    induction c using Quotient.inductionOn with
    | h Q' =>
      change classOf Q' ∈ genusClasses Q ↔ classOf Q' ∈ ({classOf Q} : Set (QClass 0))
      rw [quadForm_zero_eq Q' Q]
      simp [classOf_self_mem_genusClasses]
  have hm : Siegel.mass Q = 1 := by
    rw [Siegel.mass, hcl, finsum_mem_singleton, QClass.autCard_classOf, card_aut_dim_zero]; norm_num
  refine ⟨?_, hm⟩
  rw [hm]; simp

end QuadFormsKB.ConwaySloane.Mass
