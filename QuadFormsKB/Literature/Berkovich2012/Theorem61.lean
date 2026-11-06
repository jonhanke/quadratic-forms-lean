import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Berkovich2012.SGenus
import QuadFormsKB.Literature.Berkovich2012.UnitSquare
import QuadFormsKB.Literature.Berkovich2012.LocalDensities
import QuadFormsKB.Literature.Berkovich2012.Lemma42
import QuadFormsKB.Literature.Berkovich2012.Lemma31
import QuadFormsKB.Siegel.FourSquares
import QuadFormsKB.Siegel.FourSquaresClassNumber
import QuadFormsKB.Siegel.GenusFinite
import QuadFormsKB.Tamagawa.RatHeadline3Uncond
import QuadFormsKB.Tamagawa.OrbitalEuler
import QuadFormsKB.LocalDensity.Bridge

/-!
# Berkovich–Hanke–Jagy, Theorem 6.1 and Corollary 6.2: the S-genus identities

Source: A. Berkovich, J. Hanke and W. Jagy, *A proof of the S-genus identities for ternary quadratic
forms*, arXiv:1010.1926v2 (bib key `berkovich2012`), §6, Theorem 6.1 and Corollary 6.2, p. 7.

For $S$ odd squarefree, $W \mid S$, and $m \equiv 1, 2 \pmod 4$ with $W \mid m$:
$$\sum_{Q \in S\text{-genus}} \epsilon_W(Q) \frac{r_Q(m)}{|\mathrm{Aut}(Q)|} =
W \frac{r_{x^2+y^2+z^2}(m/W^2)}{48}$$
(both sides $0$ if $W^2 \nmid m$). The sum runs over the classes of the S-genus.

## Proof (the source's)
Siegel's formula for each genus $G$ of the S-genus (here: `siegelFormula3_natural_rat_uncond`, the
unconditional ternary Siegel formula with the natural-order Euler product) writes the genus sum as
$\mathrm{Mass}(G)\,\beta_\infty(G; m) \prod_p \beta_p(G; m)$. At $p \nmid 2S$, $G$ is locally
$x^2+y^2+z^2$, so the products differ only at $p \mid 2S$ (`eulerProductValue_ratio`); with the local
densities (Lemmas 4.1–4.3), the masses (Lemma 5.1) and $\det = 4S^2$, the sum over the $2^r$ genera
factors prime by prime, and each factor is evaluated by Lemma 6.3.

## Inputs
* `SGenusStructure S B` (named statement): Lemma 3.3 (the parametrization of the genera of the S-genus by
  signs) and the parts of Lemma 3.1 at $p \mid 2S$; the part at $p \nmid 2S$ and Definition 3.2's signs
  are proved (`local_good_of_disc`, `QClass.epsP_eq_legendre`). In `Final.lean` it is derived from
  Lemma 3.3 alone (`SGenusParam.toStructure`).
* `SGenusMass S B`: Lemma 5.1, the masses, as a named statement; proved from `SGenusStructure` in
  `Mass.lean` (`lemma_5_1`). The final `theorem_6_1` and `corollary_6_2` are in `Final.lean`.
* `Lemma41`, `Lemma42`, `Lemma43`: the local density lemmas as named statements; all three are
  proved (`lemma41_holds`, `lemma42_holds`, `lemma43_holds`) and discharged inside `theorem_6_1_of_mass`.
-/

namespace QuadFormsKB.Berkovich2012

open QuadFormsKB QuadFormsKB.Siegel QuadFormsKB.LocalDensity Filter Topology

/-- The sign vectors $(\varepsilon_p)_{p \mid S}$, as Booleans ($\mathtt{true} \mapsto +1$). -/
abbrev Signs (S : ℕ) : Type := {p // p ∈ S.primeFactors} → Bool

/-- The sign $\pm 1$ of a Boolean. -/
def sgnB (b : Bool) : ℤ := if b then 1 else -1

/-- **Lemmas 3.1 and 3.3** (named statement: local structure and parametrization of the genera of the
S-genus). Not a headline input any more: for $S$ odd squarefree it follows from Lemma 3.3 alone
(`SGenusParam.toStructure` in `Final.lean`; the local fields are proved there by `local_odd_of_disc`,
`local_two_of_disc`). `B σ` are positive definite binary forms of discriminant $-8S$, one for each sign vector
$\sigma = (\varepsilon_p)_{p \mid S}$, such that the genera of the ternary forms
$B_\sigma(x, y) + 2Sz^2$ are pairwise distinct and exhaust the S-genus, with local structure
(Lemma 3.1): $\sim_{\mathbb{Z}_p} \alpha x^2 + \alpha p y^2 + p z^2$ with
$\left(\frac{-\alpha}{p}\right) = \varepsilon_p$ for $p \mid S$, and
$\sim_{\mathbb{Z}_2} u x^2 + 2u y^2 + 2z^2$ with $u$ odd (the form used in Lemma 4.3).

The other parts of Lemma 3.1 and Definition 3.2 are proved: $\sim_{\mathbb{Z}_p} x^2+y^2+z^2$ for
$p \nmid 2S$ (`local_good_of_disc`), and every class of the genus has the signs $\varepsilon_p$
(`QClass.epsP_eq_legendre`). -/
@[kb "berkovich2012" "§3, Lemmas 3.1 and 3.3, pp. 2–3"]
structure SGenusStructure (S : ℕ) (B : Signs S → BinQF) : Prop where
  posDef : ∀ σ, (B σ).PosDef'
  disc : ∀ σ, (B σ).disc = -8 * S
  cover : SGenus S ⊆ ⋃ σ, genusClasses (sForm S (B σ))
  disjoint : ∀ σ τ, σ ≠ τ →
    Disjoint (genusClasses (sForm S (B σ))) (genusClasses (sForm S (B τ)))
  local_odd : ∀ σ (p : {p // p ∈ S.primeFactors}),
    haveI : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    ∃ α : ℤ, ¬ ((p : ℕ) : ℤ) ∣ α ∧ legendreSym p (-α) = sgnB (σ p) ∧
      IsometricGL ((sForm S (B σ)).map (Int.castRingHom ℤ_[p]))
        ((QuadForm.diag ![α, α * p, (p : ℤ)]).map (Int.castRingHom ℤ_[p]))
  local_two : ∀ σ, ∃ u : ℤ, Odd u ∧
    IsometricGL ((sForm S (B σ)).map (Int.castRingHom ℤ_[2]))
      ((QuadForm.diag ![u, 2 * u, 2]).map (Int.castRingHom ℤ_[2]))

/-- **Lemma 5.1** (named statement; proved from `SGenusStructure` by `lemma_5_1` in `Mass.lean`):
the masses of the genera of the S-genus, from the Conway–Sloane mass
formula): $\mathrm{Mass}(G_\sigma) = \frac1{16} \prod_{p \mid S} \frac{p + \varepsilon_p}{2}$. -/
@[kb "berkovich2012" "§5, Lemma 5.1, p. 6"]
structure SGenusMass (S : ℕ) (B : Signs S → BinQF) : Prop where
  mass_eq : ∀ σ, mass (sForm S (B σ)) =
    (1 / 16 : ℝ) * ∏ p : {p // p ∈ S.primeFactors}, ((p : ℝ) + sgnB (σ p)) / 2

/-- **Lemma 4.1** (named statement): for an odd prime $p$ and $m \ne 0$,
$\beta_{x^2+y^2+z^2,\,p}(m)$ is given by `beta3`. -/
@[kb "berkovich2012" "§4, Lemma 4.1, p. 4"]
structure Lemma41 : Prop where
  holds : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ m : ℤ, m ≠ 0 →
    localDensity (sumSq 3) p m = (beta3 p m : ℝ)

/-- **Lemma 4.2** (named statement): for an odd prime $p$, $p \nmid \alpha$ and $m \ne 0$,
$\beta_{\alpha x^2 + \alpha p y^2 + p z^2,\,p}(m)$ is given by `betaG` with
$\varepsilon = \left(\frac{-\alpha}{p}\right)$. -/
@[kb "berkovich2012" "§4, Lemma 4.2, p. 4"]
structure Lemma42 : Prop where
  holds : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ α : ℤ, ¬ (p : ℤ) ∣ α → ∀ m : ℤ, m ≠ 0 →
    localDensity (QuadForm.diag ![α, α * p, (p : ℤ)]) p m = (betaG p (legendreSym p (-α)) m : ℝ)

/-- **Lemma 4.3** (named statement, the part used): for $m \equiv 1, 2 \pmod 4$,
$\beta_{x^2+y^2+z^2,\,2}(m) = 3/2$ and $\beta_{u x^2 + 2u y^2 + 2z^2,\,2}(m) = 1$ ($u$ odd). -/
@[kb "berkovich2012" "§4, Lemma 4.3, p. 5"]
structure Lemma43 : Prop where
  three : ∀ m : ℤ, (m % 4 = 1 ∨ m % 4 = 2) → localDensity (sumSq 3) 2 m = 3 / 2
  genus : ∀ u : ℤ, Odd u → ∀ m : ℤ, (m % 4 = 1 ∨ m % 4 = 2) →
    localDensity (QuadForm.diag ![u, 2 * u, 2]) 2 m = 1


/-! ### Local and archimedean ingredients -/

lemma sgnB_sq (b : Bool) : sgnB b ^ 2 = 1 := by cases b <;> simp [sgnB]

/-- $\beta_p$ is invariant under $\mathbb{Z}_p$-equivalence. -/
lemma localDensity_eq_of_padic_equiv {n : ℕ} {Q Q' : QuadForm ℤ n} (p : ℕ) [Fact p.Prime]
    (h : IsometricGL (Q.map (Int.castRingHom ℤ_[p])) (Q'.map (Int.castRingHom ℤ_[p]))) (m : ℤ) :
    localDensity Q p m = localDensity Q' p m := by
  rw [localDensity_eq_padic, localDensity_eq_padic]
  exact Tamagawa.localDensity_congr_isometricGL h _ _

/-- `B(x, y) + 2Sz^2` in coordinates. -/
lemma sForm_eval (S : ℕ) (B : BinQF) (x : Fin 3 → ℤ) :
    QuadForm.eval (sForm S B) x = B.a * x 0 ^ 2 + B.b * x 0 * x 1 + B.c * x 1 ^ 2 + 2 * S * x 2 ^ 2 := by
  simp [sForm, QuadForm.eval, QuadForm.evalIn, QuadForm.ofUpper, Fin.sum_univ_three]
  ring

/-- `B(x, y) + 2Sz^2` is positive definite for $B$ positive definite and $S \ge 1$. -/
lemma sForm_posDef {S : ℕ} (hS : 0 < S) {B : BinQF} (hB : B.PosDef') : IntQF.PosDef (sForm S B) := by
  intro x hx
  rw [sForm_eval]
  obtain ⟨ha, hd⟩ := hB
  have hd' : B.b ^ 2 - 4 * B.a * B.c < 0 := hd
  have key : 4 * B.a * (B.a * x 0 ^ 2 + B.b * x 0 * x 1 + B.c * x 1 ^ 2) =
      (2 * B.a * x 0 + B.b * x 1) ^ 2 + (4 * B.a * B.c - B.b ^ 2) * x 1 ^ 2 := by ring
  have hbin : 0 ≤ B.a * x 0 ^ 2 + B.b * x 0 * x 1 + B.c * x 1 ^ 2 := by
    have : 0 ≤ 4 * B.a * (B.a * x 0 ^ 2 + B.b * x 0 * x 1 + B.c * x 1 ^ 2) := by
      rw [key]; have := sq_nonneg (x 1); nlinarith [sq_nonneg (2 * B.a * x 0 + B.b * x 1)]
    nlinarith
  have hS' : (0 : ℤ) < S := by exact_mod_cast hS
  by_cases h2 : x 2 = 0
  · have h01 : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h; push Not at h
      exact hx (funext fun i => by fin_cases i <;> simp [h.1, h.2, h2])
    rw [h2]
    have : 0 < 4 * B.a * (B.a * x 0 ^ 2 + B.b * x 0 * x 1 + B.c * x 1 ^ 2) := by
      rw [key]
      rcases h01 with h | h
      · by_cases h1 : x 1 = 0
        · rw [h1]; simp; positivity
        · have : 0 < (4 * B.a * B.c - B.b ^ 2) * x 1 ^ 2 := by
            have : 0 < x 1 ^ 2 := by positivity
            nlinarith
          nlinarith [sq_nonneg (2 * B.a * x 0 + B.b * x 1)]
      · have : 0 < (4 * B.a * B.c - B.b ^ 2) * x 1 ^ 2 := by
          have : 0 < x 1 ^ 2 := by positivity
          nlinarith
        nlinarith [sq_nonneg (2 * B.a * x 0 + B.b * x 1)]
    have : 0 < B.a * x 0 ^ 2 + B.b * x 0 * x 1 + B.c * x 1 ^ 2 := by nlinarith
    simpa using this
  · have : 0 < x 2 ^ 2 := by positivity
    nlinarith

/-- The Gram determinant of `B(x,y) + 2Sz^2` with $\operatorname{disc} B = -8S$ is $4S^2$. -/
lemma gramDet_sForm (S : ℕ) (B : BinQF) (hd : B.disc = -8 * S) : gramDet (sForm S B) = 4 * S ^ 2 := by
  unfold gramDet
  have : (sForm S B).hessian.det = 32 * S ^ 2 := by
    simp [sForm, QuadForm.hessian, QuadForm.ofUpper, Matrix.det_fin_three]
    have : B.b ^ 2 - 4 * B.a * B.c = -8 * S := hd
    nlinarith
  rw [this]; push_cast; ring

/-- The Gram determinant of $x^2 + y^2 + z^2$ is $1$. -/
lemma gramDet_sumSq_three : gramDet (sumSq 3) = 1 := by
  unfold gramDet
  have : (sumSq 3).hessian.det = 8 := by
    simp [sumSq, QuadForm.hessian, QuadForm.diag, Matrix.det_fin_three]
  rw [this]; norm_num

/-- $\beta_\infty$ of the S-genus forms: $\beta_\infty(B + 2Sz^2; m) = \beta_\infty(x^2+y^2+z^2; m)/(2S)$
(Lemma 4.4, $\beta_{Q,\infty}(m) = C_n \det(Q)^{-1/2} m^{(n-2)/2}$, with $\det = 4S^2$). -/
@[kb "berkovich2012" "§4, Lemma 4.4, p. 5"]
lemma betaInf_sForm (S : ℕ) (hS : 0 < S) (B : BinQF) (hd : B.disc = -8 * S) (m : ℝ) :
    betaInf (sForm S B) m = betaInf (sumSq 3) m / (2 * S) := by
  unfold betaInf
  rw [gramDet_sForm S B hd, gramDet_sumSq_three, Real.one_rpow]
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have : ((4 : ℝ) * S ^ 2) ^ (-(1 / 2 : ℝ)) = 1 / (2 * S) := by
    rw [show (4 : ℝ) * S ^ 2 = (2 * S) ^ (2 : ℝ) by rw [Real.rpow_two]; ring]
    rw [← Real.rpow_mul (by positivity)]
    norm_num
    rw [Real.rpow_neg_one]; ring
  rw [this]
  field_simp

/-- $\beta_\infty(x^2+y^2+z^2; m / W^2) = \beta_\infty(x^2+y^2+z^2; m)/W$. -/
lemma betaInf_sumSq_div (W : ℕ) (hW : 0 < W) {m : ℝ} (hm : 0 ≤ m) :
    betaInf (sumSq 3) (m / (W : ℝ) ^ 2) = betaInf (sumSq 3) m / W := by
  unfold betaInf
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have h1 : (((3 : ℕ) : ℝ) - 2) / 2 = 1 / 2 := by norm_num
  rw [h1, Real.div_rpow hm (by positivity), show ((W : ℝ) ^ 2) ^ (1 / 2 : ℝ) = W by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW'.le]; norm_num]
  field_simp


/-! ### The local density lemmas hold -/

/-- `Lemma41` holds (`localDensity_sumSq_three_odd`). -/
theorem lemma41_holds : Lemma41 :=
  ⟨fun p _ hp m hm => by rw [localDensity_sumSq_three_odd p hp m hm]⟩

/-- `Lemma43` holds (`localDensity_sumSq_three_two_paper`, `localDensity_diag_u_two`). -/
theorem lemma43_holds : Lemma43 :=
  ⟨fun m hm => (localDensity_sumSq_three_two_paper m).1 hm,
    fun _ hu m hm => (localDensity_diag_u_two hu m).1 hm⟩

/-- `Lemma42` holds (`lemma42`). -/
theorem lemma42_holds : Lemma42 :=
  ⟨fun p _ hp α hα m hm => lemma42 p hp α hα m hm⟩

/-- $\beta_{x^2+y^2+z^2,\,p}(m) > 0$ (formula of Lemma 4.1) for $p$ odd and $m \ne 0$. -/
lemma beta3_pos (p : ℕ) [Fact p.Prime] {m : ℤ} (hm : m ≠ 0) : 0 < beta3 p m := by
  have hp : (2 : ℚ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hG : ∀ k, 0 ≤ geomSum p k := fun k => Finset.sum_nonneg fun j _ => by positivity
  have hG1 : ∀ k, 1 ≤ geomSum p (k + 1) := fun k => by
    unfold geomSum
    rw [Finset.sum_range_succ']
    simp only [pow_zero]
    have := Finset.sum_nonneg (s := Finset.range k) fun j _ =>
      (by positivity : (0 : ℚ) ≤ (1 / (p : ℚ)) ^ (j + 1))
    linarith
  have h1 : (0 : ℚ) < 1 - 1 / (p : ℚ) ^ 2 := by
    have : 1 / (p : ℚ) ^ 2 ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  unfold beta3
  simp only
  split_ifs with hv
  · have hp1 : 1 / (p : ℚ) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have : (0 : ℚ) < 1 + (chiOf p m : ℚ) / p := by
      rcases chiOf_eq_one_or_neg_one p hm hv with h | h <;> rw [h]
      · positivity
      · push_cast; rw [neg_div]; linarith
    have := hG (padicValInt p m / 2)
    positivity
  · have := hG1 (padicValInt p m / 2)
    nlinarith

/-- The local factors of the genus $\sigma$ outside $2S$ are those of $x^2 + y^2 + z^2$. -/
lemma factor_good {S : ℕ} {B : Signs S → BinQF} (hS : SGenusStructure S B) (σ : Signs S)
    (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ 2 * S) (m : ℤ) :
    localDensity (sForm S (B σ)) p m = localDensity (sumSq 3) p m :=
  localDensity_eq_of_padic_equiv p (local_good_of_disc p S (B σ) (hS.disc σ) hp) m

/-- The local factor at $p \mid S$ of the genus $\sigma$ is `betaG p ε_p m` (Lemma 4.2). -/
lemma factor_odd {S : ℕ} {B : Signs S → BinQF} (hS : SGenusStructure S B) (h42 : Lemma42)
    (σ : Signs S) (p : {p // p ∈ S.primeFactors}) [Fact (p : ℕ).Prime] (hp2 : (p : ℕ) ≠ 2)
    {m : ℤ} (hm : m ≠ 0) :
    localDensity (sForm S (B σ)) p m = (betaG p (sgnB (σ p)) m : ℝ) := by
  obtain ⟨α, hα, hleg, heq⟩ := hS.local_odd σ p
  rw [localDensity_eq_of_padic_equiv p heq m, h42.holds p hp2 α hα m hm, hleg]

/-- The local factor at $2$ of the genus $\sigma$ is $1$ (Lemma 4.3). -/
lemma factor_two {S : ℕ} {B : Signs S → BinQF} (hS : SGenusStructure S B) (h43 : Lemma43)
    (σ : Signs S) {m : ℤ} (hm4 : m % 4 = 1 ∨ m % 4 = 2) :
    localDensity (sForm S (B σ)) 2 m = 1 := by
  obtain ⟨u, hu, heq⟩ := hS.local_two σ
  rw [localDensity_eq_of_padic_equiv 2 heq m, h43.genus u hu m hm4]


instance factPrimeFactors {S : ℕ} (p : {p // p ∈ S.primeFactors}) : Fact (p : ℕ).Prime :=
  ⟨Nat.prime_of_mem_primeFactors p.2⟩

/-- The primes dividing $2S$, as `AWS.PrimeIdx`. -/
def primesTwoS (S : ℕ) : Finset AWS.PrimeIdx := (2 * S).primeFactors.subtype Nat.Prime

lemma mem_primesTwoS {S : ℕ} (hS : 0 < S) (p : AWS.PrimeIdx) :
    p ∈ primesTwoS S ↔ (p : ℕ) ∣ 2 * S := by
  simp only [primesTwoS, Finset.mem_subtype, Nat.mem_primeFactors]
  exact ⟨fun h => h.2.1, fun h => ⟨p.2, h, by omega⟩⟩

/-- A product over `primesTwoS S` of a function of the underlying prime is the product over $p = 2$
and the primes $p \mid S$ ($S$ odd). -/
lemma prod_primesTwoS {S : ℕ} (hS : 0 < S) (hSodd : Odd S) (f : ℕ → ℝ) :
    ∏ p ∈ primesTwoS S, f p = f 2 * ∏ p : {p // p ∈ S.primeFactors}, f p := by
  rw [primesTwoS, Finset.prod_subtype_eq_prod_filter (f := fun x : ℕ => f x)]
  rw [Finset.filter_true_of_mem fun x hx => Nat.prime_of_mem_primeFactors hx]
  rw [Nat.primeFactors_mul (by norm_num) hS.ne', Nat.prime_two.primeFactors]
  rw [Finset.prod_union]
  · rw [Finset.prod_singleton, Finset.prod_coe_sort S.primeFactors f]
  · rw [Finset.disjoint_singleton_left, Nat.mem_primeFactors]
    rintro ⟨-, h2, -⟩
    exact (Nat.not_even_iff_odd.2 hSodd) (even_iff_two_dvd.2 h2)

/-- **Siegel's formula for a genus of the S-genus, compared with $x^2 + y^2 + z^2$.** For
$m \equiv 1, 2 \pmod 4$ and $P_3$ the natural-order Euler product of $x^2+y^2+z^2$ at $m$:
$$\sum_{Q' \in G_\sigma} \frac{r_{Q'}(m)}{|\mathrm{Aut}(Q')|} = \mathrm{Mass}(G_\sigma)\,
\frac{\beta_\infty(x^2+y^2+z^2; m)}{2S}\, P_3\, \frac23 \prod_{p \mid S}
\frac{\beta_{G_\sigma,p}(m)}{\beta_{x^2+y^2+z^2,p}(m)}.$$ -/
theorem genusRepSum_sigma {S : ℕ} (hSpos : 0 < S) (hSodd : Odd S) {B : Signs S → BinQF}
    (hS : SGenusStructure S B) (h42 : Lemma42) (σ : Signs S) {m : ℤ} (hm1 : 1 ≤ m)
    (hm4 : m % 4 = 1 ∨ m % 4 = 2) {P₃ : ℝ} (hP₃ : IsEulerProductValue (sumSq 3) m P₃) :
    genusRepSum (sForm S (B σ)) m = mass (sForm S (B σ)) *
      (betaInf (sumSq 3) m / (2 * S)) * P₃ *
        ((2 / 3) * ∏ p : {p // p ∈ S.primeFactors},
          (betaG p (sgnB (σ p)) m : ℝ) / (beta3 p m : ℝ)) := by
  have hm0 : m ≠ 0 := by omega
  have hpd := sForm_posDef hSpos (hS.posDef σ)
  obtain ⟨P, hP, havg⟩ := Tamagawa.RatHeadline3.siegelFormula3_natural_rat_uncond _ hpd hm1
  have hmass : mass (sForm S (B σ)) ≠ 0 := (mass_pos hpd (genusFinite hpd)).ne'
  have hsum : genusRepSum (sForm S (B σ)) m = mass (sForm S (B σ)) * genusRepAvg (sForm S (B σ)) m := by
    unfold genusRepAvg; field_simp
  -- local factors
  have hodd : ∀ p : {p // p ∈ S.primeFactors}, (p : ℕ) ≠ 2 := fun p h => by
    have := Nat.dvd_of_mem_primeFactors p.2
    rw [h] at this
    exact (Nat.not_even_iff_odd.2 hSodd) (even_iff_two_dvd.2 this)
  have h3pos : ∀ p : {p // p ∈ S.primeFactors}, (0 : ℝ) < (beta3 p m : ℝ) := fun p => by
    exact_mod_cast beta3_pos p hm0
  have hratio := eulerProductValue_ratio hP hP₃ (primesTwoS S)
    (fun p hp => by
      have : ¬ (p : ℕ) ∣ 2 * S := fun h => hp ((mem_primesTwoS hSpos p).2 h)
      exact factor_good hS σ p this m)
    (fun p hp => by
      have hp' := (mem_primesTwoS hSpos p).1 hp
      show localDensity (sumSq 3) p m ≠ 0
      by_cases h2 : (p : ℕ) = 2
      · rw [h2, (localDensity_sumSq_three_two_paper m).1 hm4]; norm_num
      · have hpS : (p : ℕ) ∈ S.primeFactors := by
          rw [Nat.mem_primeFactors]
          refine ⟨p.2, ?_, hSpos.ne'⟩
          exact (Nat.Coprime.dvd_of_dvd_mul_left
            ((Nat.coprime_primes p.2 Nat.prime_two).2 h2) hp')
        rw [localDensity_sumSq_three_odd p h2 m hm0]
        exact (h3pos ⟨p, hpS⟩).ne')
  have hprod : ∏ p ∈ primesTwoS S, eulerFactor (sForm S (B σ)) m p / eulerFactor (sumSq 3) m p =
      (2 / 3) * ∏ p : {p // p ∈ S.primeFactors}, (betaG p (sgnB (σ p)) m : ℝ) / (beta3 p m : ℝ) := by
    simp only [eulerFactor]
    rw [prod_primesTwoS hSpos hSodd
      (fun p => localDensity (sForm S (B σ)) p m / localDensity (sumSq 3) p m)]
    rw [factor_two hS lemma43_holds σ hm4, (localDensity_sumSq_three_two_paper m).1 hm4]
    congr 1
    · norm_num
    · refine Finset.prod_congr rfl fun p _ => ?_
      rw [factor_odd hS h42 σ p (hodd p) hm0, localDensity_sumSq_three_odd p (hodd p) m hm0]
  rw [hsum, havg, aEWith, betaInf_sForm S hSpos (B σ) (hS.disc σ), hratio, hprod]
  ring


/-- Comparison of natural-order Euler products at two arguments (same proof as
`eulerProductValue_ratio`). -/
theorem eulerProductValue_ratio₂ {n : ℕ} {Q Q' : QuadForm ℤ n} {m m' : ℤ} {P P' : ℝ}
    (hP : IsEulerProductValue Q m P) (hP' : IsEulerProductValue Q' m' P')
    (T : Finset AWS.PrimeIdx) (hout : ∀ p ∉ T, eulerFactor Q m p = eulerFactor Q' m' p)
    (hne : ∀ p ∈ T, eulerFactor Q' m' p ≠ 0) :
    P = P' * ∏ p ∈ T, eulerFactor Q m p / eulerFactor Q' m' p := by
  set c := ∏ p ∈ T, eulerFactor Q m p / eulerFactor Q' m' p
  have hev : ∀ᶠ X in atTop, eulerPartialProd Q m X = c * eulerPartialProd Q' m' X := by
    have := tendsto_primesUpTo.eventually (eventually_ge_atTop T)
    filter_upwards [this] with X hX
    unfold eulerPartialProd
    rw [← Finset.prod_sdiff hX, ← Finset.prod_sdiff (s₁ := T) hX]
    rw [Finset.prod_congr rfl fun p hp => hout p (Finset.mem_sdiff.1 hp).2]
    have : ∏ p ∈ T, eulerFactor Q m p = c * ∏ p ∈ T, eulerFactor Q' m' p := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun p hp => by field_simp [hne p hp]
    rw [this]; ring
  have h2 : Tendsto (eulerPartialProd Q m) atTop (𝓝 (c * P')) :=
    (hP'.const_mul c).congr' (hev.mono fun X hX => hX.symm)
  have := tendsto_nhds_unique hP h2
  rw [this]; ring

/-- $r_{x^2+y^2+z^2}(m) = \beta_\infty(m) P_3(m)$ (Siegel's formula; class number one). -/
lemma repNum_sumSq_three_eq {m : ℤ} {P : ℝ} (hP : IsEulerProductValue (sumSq 3) m P) (hm1 : 1 ≤ m) :
    (repNum (sumSq 3) m : ℝ) = betaInf (sumSq 3) m * P := by
  have h3 : IntQF.PosDef (sumSq 3) := posDef_sumSq
  obtain ⟨P', hP', havg⟩ := Tamagawa.RatHeadline3.siegelFormula3_natural_rat_uncond _ h3 hm1
  have : P = P' := tendsto_nhds_unique hP hP'
  rw [this, ← genusRepAvg_of_classNumber_one h3 (genusClasses_sumSq (by norm_num)) m, havg, aEWith]

/-- **The right-hand side of (4) through Siegel's formula:** for $W \mid S$ squarefree odd,
$W^2 \mid m$, $m \ge 1$: $W\, r_3(m/W^2) = r_3(m) \prod_{p \mid W} \beta_{3,p}(m/p^2)/\beta_{3,p}(m)$. -/
lemma rhs_eq {W : ℕ} (hW0 : 0 < W) (hWodd : Odd W) (hWsf : Squarefree W) {m : ℕ} (hm1 : 1 ≤ m)
    (hW2 : W ^ 2 ∣ m) :
    (W : ℝ) * repNum (sumSq 3) ((m / W ^ 2 : ℕ) : ℤ) = repNum (sumSq 3) (m : ℤ) *
      ∏ p ∈ W.primeFactors, (localDensity (sumSq 3) p ((m : ℤ) / (p : ℤ) ^ 2) /
        localDensity (sumSq 3) p m) := by
  obtain ⟨k, hk⟩ := hW2
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h] at hk; omega
    · exact h
  have hmk : m / W ^ 2 = k := by rw [hk]; exact Nat.mul_div_cancel_left _ (by positivity)
  rw [hmk]
  obtain ⟨P, hP, -⟩ := Tamagawa.RatHeadline3.siegelFormula3_natural_rat_uncond _ posDef_sumSq
    (show (1 : ℤ) ≤ m by exact_mod_cast hm1)
  obtain ⟨Pk, hPk, -⟩ := Tamagawa.RatHeadline3.siegelFormula3_natural_rat_uncond _ posDef_sumSq
    (show (1 : ℤ) ≤ k by exact_mod_cast hk1)
  rw [repNum_sumSq_three_eq hPk (by exact_mod_cast hk1),
    repNum_sumSq_three_eq hP (by exact_mod_cast hm1)]
  -- archimedean factor
  have hbi : betaInf (sumSq 3) ((k : ℤ) : ℝ) = betaInf (sumSq 3) ((m : ℤ) : ℝ) / W := by
    rw [← betaInf_sumSq_div W hW0 (by positivity)]
    congr 1
    rw [hk]; push_cast; field_simp
  -- the Euler products
  set T : Finset AWS.PrimeIdx := W.primeFactors.subtype Nat.Prime
  have hW2odd : ∀ p ∈ W.primeFactors, p ≠ 2 := fun p hp h => by
    have := Nat.dvd_of_mem_primeFactors hp
    rw [h] at this
    exact (Nat.not_even_iff_odd.2 hWodd) (even_iff_two_dvd.2 this)
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hratio := eulerProductValue_ratio₂ hPk hP T
    (fun p hp => by
      have hpW : ¬ (p : ℕ) ∣ W := fun h => hp (by
        simp only [T, Finset.mem_subtype, Nat.mem_primeFactors]; exact ⟨p.2, h, hW0.ne'⟩)
      show localDensity (sumSq 3) p (k : ℤ) = localDensity (sumSq 3) p (m : ℤ)
      have : (m : ℤ) = (W : ℤ) ^ 2 * k := by rw [hk]; push_cast; ring
      rw [this, localDensity_unit_sq_mul _ _ (by exact_mod_cast hpW)])
    (fun p hp => by
      have hpW : (p : ℕ) ∈ W.primeFactors := by
        simpa [T, Finset.mem_subtype] using hp
      show localDensity (sumSq 3) p (m : ℤ) ≠ 0
      rw [localDensity_sumSq_three_odd p (hW2odd p hpW) _ hm0]
      exact_mod_cast (beta3_pos p hm0).ne')
  have hprodT : ∏ p ∈ T, eulerFactor (sumSq 3) (k : ℤ) p / eulerFactor (sumSq 3) (m : ℤ) p =
      ∏ p ∈ W.primeFactors, (localDensity (sumSq 3) p ((m : ℤ) / (p : ℤ) ^ 2) /
        localDensity (sumSq 3) p m) := by
    simp only [eulerFactor, T]
    rw [Finset.prod_subtype_eq_prod_filter (f := fun x : ℕ =>
      localDensity (sumSq 3) x (k : ℤ) / localDensity (sumSq 3) x (m : ℤ))]
    rw [Finset.filter_true_of_mem fun x hx => Nat.prime_of_mem_primeFactors hx]
    refine Finset.prod_congr rfl fun p hp => ?_
    congr 1
    -- m / p² = (W/p)² k with p ∤ W/p
    have hpW := Nat.dvd_of_mem_primeFactors hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    obtain ⟨w, hw⟩ := hpW
    have hpw : ¬ p ∣ w := by
      intro h
      have : p * p ∣ W := by rw [hw]; exact Nat.mul_dvd_mul_left p h
      exact hpp.one_lt.ne' (Nat.isUnit_iff.1 (hWsf p this))
    have hmw : (m : ℤ) / (p : ℤ) ^ 2 = (w : ℤ) ^ 2 * k := by
      rw [hk, hw]; push_cast
      rw [show ((p : ℤ) * w) ^ 2 * k = (p : ℤ) ^ 2 * ((w : ℤ) ^ 2 * k) by ring,
        Int.mul_ediv_cancel_left _ (pow_ne_zero 2 (by exact_mod_cast hpp.ne_zero))]
    haveI := Fact.mk hpp
    rw [hmw, localDensity_unit_sq_mul _ _ (by exact_mod_cast hpw)]
  rw [hbi, hratio, hprodT]
  have hW' : (W : ℝ) ≠ 0 := by exact_mod_cast hW0.ne'
  field_simp

/-- **Theorem 6.1 (the twisted S-genus identity).** Let $S$ be an odd squarefree natural number,
$W \mid S$, and $m \in \mathbb{N}$ with $W \mid m$ and $m \equiv 1, 2 \pmod 4$. Then
$$\sum_{Q \in S\text{-genus}} \epsilon_W(Q)\, \frac{r_Q(m)}{|\mathrm{Aut}(Q)|} =
W\, \frac{r_{x^2+y^2+z^2}(m/W^2)}{48},$$
where the right side is $0$ if $W^2 \nmid m$. The sum is over the classes of the S-genus
(`SGenus`), $\epsilon_W = \prod_{p \mid W} \varepsilon_p$ (`QClass.epsW`).

Here with the masses `SGenusMass S B` (Lemma 5.1) as a hypothesis; `theorem_6_1` (`Final.lean`)
discharges it by `lemma_5_1`. Siegel's formula and Lemmas 4.1, 4.2, 4.3, 6.3 are proved. -/
theorem theorem_6_1_of_mass {S : ℕ} (hSodd : Odd S) (hSsf : Squarefree S) {B : Signs S → BinQF}
    (hS : SGenusStructure S B) (hM : SGenusMass S B) {W : ℕ} (hW : W ∣ S)
    {m : ℕ} (hWm : W ∣ m) (hm4 : m % 4 = 1 ∨ m % 4 = 2) :
    ∑ᶠ c ∈ SGenus S, (QClass.epsW W c : ℝ) * c.repNum m / c.autCard =
      W * (if W ^ 2 ∣ m then (repNum (sumSq 3) ((m / W ^ 2 : ℕ) : ℤ) : ℝ) else 0) / 48 := by
  classical
  have h42 := lemma42_holds
  have hSpos : 0 < S := hSodd.pos
  have hm1 : 1 ≤ m := by omega
  have hm1' : (1 : ℤ) ≤ m := by exact_mod_cast hm1
  have hm0 : (m : ℤ) ≠ 0 := by omega
  have hm4' : (m : ℤ) % 4 = 1 ∨ (m : ℤ) % 4 = 2 := by omega
  have hW0 : 0 < W := Nat.pos_of_dvd_of_pos hW hSpos
  have hWodd : Odd W := hSodd.of_dvd_nat hW
  have hWsf : Squarefree W := hSsf.squarefree_of_dvd hW
  obtain ⟨P₃, hP₃, -⟩ := Tamagawa.RatHeadline3.siegelFormula3_natural_rat_uncond _ posDef_sumSq hm1'
  have hr3 := repNum_sumSq_three_eq hP₃ hm1'
  -- the S-genus is the disjoint union of the genera G_σ
  have hSG : SGenus S = ⋃ σ, genusClasses (sForm S (B σ)) :=
    Set.Subset.antisymm hS.cover (Set.iUnion_subset fun σ c hc => ⟨B σ, hS.posDef σ, hS.disc σ, hc⟩)
  have hfin : ∀ σ, (genusClasses (sForm S (B σ))).Finite := fun σ =>
    (genusFinite (sForm_posDef hSpos (hS.posDef σ))).finite_classes
  -- the sign ε_W on G_σ
  let sW : Signs S → ℝ := fun σ =>
    ∏ p : {p // p ∈ S.primeFactors}, (if (p : ℕ) ∣ W then (sgnB (σ p) : ℝ) else 1)
  have hWS : ∀ p ∈ W.primeFactors, p ∈ S.primeFactors := fun p hp =>
    Nat.mem_primeFactors.2 ⟨Nat.prime_of_mem_primeFactors hp,
      (Nat.dvd_of_mem_primeFactors hp).trans hW, hSpos.ne'⟩
  have hfilt : S.primeFactors.filter (· ∣ W) = W.primeFactors := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hp, -, -⟩, h⟩; exact ⟨hp, h, hW0.ne'⟩
    · rintro ⟨hp, h, -⟩; exact ⟨⟨hp, h.trans hW, hSpos.ne'⟩, h⟩
  -- products over the primes of S restricted to p ∣ W
  have hprodW : ∀ h : ℕ → ℝ, ∏ p : {p // p ∈ S.primeFactors}, (if (p : ℕ) ∣ W then h p else 1) =
      ∏ p ∈ W.primeFactors, h p := by
    intro h
    rw [Finset.prod_coe_sort S.primeFactors (fun p => if p ∣ W then h p else 1), Finset.prod_ite,
      Finset.prod_const_one, mul_one, hfilt]
  have heps : ∀ σ, ∀ c ∈ genusClasses (sForm S (B σ)), (QClass.epsW W c : ℝ) = sW σ := by
    intro σ c hc
    unfold QClass.epsW
    push_cast
    rw [Finset.prod_congr rfl (g := fun p : {p // p ∈ W.primeFactors} =>
      (sgnB (σ ⟨p, hWS p p.2⟩) : ℝ)) fun p _ => by
        obtain ⟨α, hα, hleg, heq⟩ := hS.local_odd σ ⟨p, hWS p p.2⟩
        have := QClass.epsP_eq_legendre (p : ℕ) hα heq hc
        rw [this]
        exact_mod_cast hleg]
    simp only [sW]
    set h : ℕ → ℝ := fun p => if h : p ∈ S.primeFactors then (sgnB (σ ⟨p, h⟩) : ℝ) else 1
    rw [show (∏ p : {p // p ∈ S.primeFactors}, if (p : ℕ) ∣ W then (sgnB (σ p) : ℝ) else 1) =
        ∏ p : {p // p ∈ S.primeFactors}, (if (p : ℕ) ∣ W then h p else 1) from
      Finset.prod_congr rfl fun p _ => by simp only [h, dif_pos p.2]]
    rw [hprodW h, ← Finset.prod_attach W.primeFactors]
    refine Finset.prod_congr rfl fun p _ => ?_
    simp only [h, dif_pos (hWS p p.2)]
  -- Step 1: the sum over the S-genus as a sum over the genera
  have hLHS : ∑ᶠ c ∈ SGenus S, (QClass.epsW W c : ℝ) * c.repNum m / c.autCard =
      ∑ σ, sW σ * genusRepSum (sForm S (B σ)) m := by
    rw [hSG, finsum_mem_iUnion (fun σ τ h => hS.disjoint σ τ h) hfin, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [genusRepSum, mul_finsum_mem]
    refine finsum_mem_congr rfl fun c hc => ?_
    rw [heps σ c hc]; push_cast; ring
  -- Step 2: Siegel's formula for each genus
  have hodd : ∀ p : {p // p ∈ S.primeFactors}, (p : ℕ) ≠ 2 := fun p h => by
    have := Nat.dvd_of_mem_primeFactors p.2
    rw [h] at this
    exact (Nat.not_even_iff_odd.2 hSodd) (even_iff_two_dvd.2 this)
  have h3pos : ∀ p : {p // p ∈ S.primeFactors}, (0 : ℝ) < (beta3 p m : ℝ) := fun p => by
    exact_mod_cast beta3_pos p hm0
  -- the local factor at p ∣ S, summed over ε_p (Lemma 6.3)
  let f : (p : {p // p ∈ S.primeFactors}) → Bool → ℝ := fun p b =>
    (if (p : ℕ) ∣ W then (sgnB b : ℝ) else 1) * (((p : ℝ) + sgnB b) / 2) *
      ((betaG p (sgnB b) m : ℝ) / (beta3 p m : ℝ))
  have hfsum : ∀ p : {p // p ∈ S.primeFactors}, ∑ b, f p b =
      (p : ℝ) * (if (p : ℕ) ∣ W then (beta3Div p m : ℝ) / (beta3 p m : ℝ) else 1) := by
    intro p
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : (p : ℕ).Prime).ne_zero
    have hb := (h3pos p).ne'
    rw [Fintype.sum_bool]
    simp only [f, sgnB, ite_true, Bool.false_eq_true, ite_false]
    split_ifs with hpW
    · have hpm : ((p : ℕ) : ℤ) ∣ m := by exact_mod_cast hpW.trans hWm
      have e := lemma63_signed_sum p (hodd p) hm0 hpm
      have e' : (betaG p 1 m : ℝ) * (p + 1) / (2 * p) - (betaG p (-1) m : ℝ) * (p - 1) / (2 * p) =
          (beta3Div p m : ℝ) := by exact_mod_cast e
      field_simp
      push_cast at e' ⊢
      field_simp at e'
      linear_combination e'
    · have e := lemma63_sum p (hodd p) hm0
      have e' : (betaG p 1 m : ℝ) * (p + 1) / (2 * p) + (betaG p (-1) m : ℝ) * (p - 1) / (2 * p) =
          (beta3 p m : ℝ) := by exact_mod_cast e
      field_simp
      push_cast at e' ⊢
      field_simp at e'
      linear_combination e'
  have hfactor : ∑ σ : Signs S, sW σ *
      ((1 / 16 : ℝ) * ∏ p : {p // p ∈ S.primeFactors}, ((p : ℝ) + sgnB (σ p)) / 2) *
        (∏ p : {p // p ∈ S.primeFactors}, (betaG p (sgnB (σ p)) m : ℝ) / (beta3 p m : ℝ)) =
      (1 / 16) * ∏ p : {p // p ∈ S.primeFactors}, ∑ b, f p b := by
    rw [← Finset.sum_prod_piFinset Finset.univ f, Fintype.piFinset_univ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [sW, f, Finset.prod_mul_distrib]
    ring
  have hprodS : ∏ p : {p // p ∈ S.primeFactors}, (p : ℝ) = S := by
    rw [Finset.prod_coe_sort S.primeFactors (fun p => (p : ℝ)), ← Nat.cast_prod,
      Nat.prod_primeFactors_of_squarefree hSsf]
  have hLHS' : ∑ᶠ c ∈ SGenus S, (QClass.epsW W c : ℝ) * c.repNum m / c.autCard =
      (repNum (sumSq 3) (m : ℤ) : ℝ) / 48 *
        ∏ p : {p // p ∈ S.primeFactors},
          (if (p : ℕ) ∣ W then (beta3Div p m : ℝ) / (beta3 p m : ℝ) else 1) := by
    rw [hLHS]
    have e : ∀ σ : Signs S, sW σ * genusRepSum (sForm S (B σ)) m =
        (betaInf (sumSq 3) ((m : ℤ) : ℝ) / (2 * S) * P₃ * (2 / 3)) *
          (sW σ * ((1 / 16 : ℝ) * ∏ p : {p // p ∈ S.primeFactors}, ((p : ℝ) + sgnB (σ p)) / 2) *
            (∏ p : {p // p ∈ S.primeFactors}, (betaG p (sgnB (σ p)) m : ℝ) / (beta3 p m : ℝ))) := by
      intro σ
      rw [genusRepSum_sigma hSpos hSodd hS h42 σ hm1' hm4' hP₃, hM.mass_eq σ]
      ring
    rw [Finset.sum_congr rfl fun σ _ => e σ, ← Finset.mul_sum, hfactor,
      Finset.prod_congr rfl fun p _ => hfsum p, Finset.prod_mul_distrib, hprodS, hr3]
    have hS0 : (S : ℝ) ≠ 0 := by exact_mod_cast hSpos.ne'
    field_simp
    ring
  rw [hLHS']
  split_ifs with hW2
  · -- W² ∣ m: compare with Siegel's formula at m / W²
    have hr := rhs_eq hW0 hWodd hWsf hm1 hW2
    have hp2 : ∀ p : {p // p ∈ S.primeFactors}, (p : ℕ) ∣ W → ((p : ℕ) : ℤ) ^ 2 ∣ (m : ℤ) := by
      intro p hpW
      have : (p : ℕ) ^ 2 ∣ m := (pow_dvd_pow_of_dvd hpW 2).trans hW2
      exact_mod_cast this
    have hcongr : ∏ p : {p // p ∈ S.primeFactors},
        (if (p : ℕ) ∣ W then (beta3Div p m : ℝ) / (beta3 p m : ℝ) else 1) =
        ∏ p : {p // p ∈ S.primeFactors}, (if (p : ℕ) ∣ W then
          localDensity (sumSq 3) p ((m : ℤ) / ((p : ℕ) : ℤ) ^ 2) /
            localDensity (sumSq 3) p m else 1) := by
      refine Finset.prod_congr rfl fun p _ => ?_
      split_ifs with hpW
      · have hd := hp2 p hpW
        have hq0 : (m : ℤ) / ((p : ℕ) : ℤ) ^ 2 ≠ 0 := by
          obtain ⟨q, hq⟩ := hd
          rw [hq, Int.mul_ediv_cancel_left _ (pow_ne_zero 2 (by exact_mod_cast
            (Fact.out : (p : ℕ).Prime).ne_zero))]
          rintro rfl; simp at hq; omega
        rw [localDensity_sumSq_three_odd p (hodd p) _ hq0,
          localDensity_sumSq_three_odd p (hodd p) _ hm0, beta3Div, if_pos hd]
      · rfl
    rw [hcongr, hprodW (fun p => localDensity (sumSq 3) p ((m : ℤ) / (p : ℤ) ^ 2) /
      localDensity (sumSq 3) p m)]
    linear_combination (-1 / 48 : ℝ) * hr
  · -- W² ∤ m: some p ∣ W has p² ∤ m, and both sides vanish
    have hex : ∃ p ∈ W.primeFactors, ¬ p ^ 2 ∣ m := by
      by_contra hall
      push Not at hall
      apply hW2
      have hWsq : W ^ 2 = ∏ p ∈ W.primeFactors, p ^ 2 := by
        rw [Finset.prod_pow, Nat.prod_primeFactors_of_squarefree hWsf]
      have hZ : (∏ p ∈ W.primeFactors, ((p : ℤ)) ^ 2) ∣ (m : ℤ) :=
        Finset.prod_dvd_of_coprime (fun p hp q hq hpq => by
          simp only [Function.onFun]
          exact Nat.isCoprime_iff_coprime.2 (by
            have := Nat.Coprime.pow 2 2 ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
              (Nat.prime_of_mem_primeFactors hq)).2 hpq)
            exact_mod_cast this)) (fun p hp => by exact_mod_cast hall p hp)
      rw [hWsq]
      exact_mod_cast hZ
    obtain ⟨p, hpW, hp2⟩ := hex
    have hzero : ∏ q : {p // p ∈ S.primeFactors},
        (if (q : ℕ) ∣ W then (beta3Div q m : ℝ) / (beta3 q m : ℝ) else 1) = 0 := by
      refine Finset.prod_eq_zero (i := ⟨p, hWS p hpW⟩) (Finset.mem_univ _) ?_
      simp only
      rw [if_pos (Nat.dvd_of_mem_primeFactors hpW), beta3Div, if_neg (by
        intro h; apply hp2; exact_mod_cast h)]
      simp
    rw [hzero]; simp


/-- **Corollary 6.2 (the S-genus identity).** For $S$ odd squarefree and $m \equiv 1, 2 \pmod 4$,
$$\sum_{Q \in S\text{-genus}} \frac{r_Q(m)}{|\mathrm{Aut}(Q)|} = \frac{r_{x^2+y^2+z^2}(m)}{48}.$$
Theorem 6.1 with $W = 1$, with the masses as a hypothesis (see `corollary_6_2` in `Final.lean`). -/
theorem corollary_6_2_of_mass {S : ℕ} (hSodd : Odd S) (hSsf : Squarefree S) {B : Signs S → BinQF}
    (hS : SGenusStructure S B) (hM : SGenusMass S B) {m : ℕ}
    (hm4 : m % 4 = 1 ∨ m % 4 = 2) :
    ∑ᶠ c ∈ SGenus S, (c.repNum m : ℝ) / c.autCard = (repNum (sumSq 3) (m : ℤ) : ℝ) / 48 := by
  have h := theorem_6_1_of_mass hSodd hSsf hS hM (one_dvd S) (one_dvd m) hm4
  have h1 : ∀ c : QClass 3, QClass.epsW 1 c = 1 := fun c =>
    Finset.prod_eq_one fun p _ => absurd p.2 (by simp)
  simp only [h1, Int.cast_one, one_mul, one_pow, one_dvd, ite_true, Nat.div_one,
    Nat.cast_one] at h
  exact h

end QuadFormsKB.Berkovich2012
