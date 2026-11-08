/-
# Hanke 2011 (enumerating maximal definite forms): Theorem 4.2, proved

J. Hanke, *Enumerating maximal definite quadratic forms of bounded class number over $\mathbb Z$ in $n\ge3$ variables*,
arXiv:1110.1876v1 (`hanke2011enumerating`), Theorem 4.2, p. 7.

**Theorem 4.2** (`theorem_4_2`): for every $n\ge3$ and every bound $B$ there are only finitely many classes of maximal
$\mathbb Z$-valued positive definite quadratic forms in $n$ variables with class number $h\le B$. **Unconditional**: this
discharges the former named statement `Theorem42` (`BoundsEven.lean`).

**Route.** The paper's proof bounds the primes at which the Gan–Hanke–Yu mass-type is not generic (Lemma 7.4 for odd $n$; Lemmas
6.1, 7.3 for the conductor of $\chi$ when $n$ is even) and concludes "finitely many products $\prod_p\lambda_p$, finitely many
masses". The last step needs that the local data determine finitely many genera; here it is made precise through the
Hessian determinant, using the same bounds:
1. $|\det H| = \prod_p[\widetilde\Lambda_p:\Lambda_p]$ (the dual indices, `dualIndexAt`; product formula, `tprod_dualIndexAt`).
2. For a maximal lattice the dual index at $p$ is $|2|_p^{-1}p^c$ with $c\in\{0,1,2\}$, $c = 0$ exactly for the generic type
   ($n$ odd, `dualIndexAt_odd`); $1$ or $p^2$ off the ramified primes, $1$ for the generic type ($n$ even,
   `dualIndexAt_even_unram`), and $p^{f_p}$ (a factor of $\mathrm{Cond}(\chi)$) at the ramified primes
   (`dualIndexAt_ram_nondyadic`, `dualIndexAt_ram_dyadic`).
3. The non-generic primes are bounded in terms of $(n, B)$: odd $n$ by `eligible_prime_bound_odd`; even $n$ by Lemma 7.4
   with the lower bound $|L(1-\frac n2,\chi)|/2^t\ge K_0(n) > 0$ from Lemma 6.1 (`eligible_prime_bound_even`), and the
   ramified primes by $\mathrm{Cond}(\chi)\le C(n,B)$ (`lemma_7_3_finite`).
4. Hence $|\det H|\le D(n, B)$ (`abs_det_le`), and Hermite's reduction (`Siegel.exists_intEquiv_hessian_bounded`, the
   positive definite case of Cassels Ch. 9 Thm 1.1) leaves finitely many forms up to $\mathrm{GL}_n(\mathbb Z)$.
-/
import QuadFormsKB.Literature.Hanke2011Enumerating.BoundsEven
import QuadFormsKB.Literature.ConwaySloane.Mass.StdForm
import QuadFormsKB.Siegel.GenusFinite
import QuadFormsKB.Tamagawa.RatBridge

open NumberField IsDedekindDomain
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2011Enumerating

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Indefinite QuadFormsKB.Hanke2005

variable {n : ℕ}

/-! ### Products bounded by a power -/

/-- A product with finite support whose factors are in $[0, M]$ ($M\ge1$) and equal to $1$ off a finite set $S$ is at most
$M^{\#S}$. -/
theorem tprod_le_pow_card {ι : Type*} {f : ι → ℝ} (S : Finset ι) (hS : ∀ v, f v ≠ 1 → v ∈ S) {M : ℝ}
    (hf0 : ∀ v, 0 ≤ f v) (hfM : ∀ v, f v ≤ M) : ∏' v, f v ≤ M ^ S.card := by
  rw [tprod_eq_prod (L := SummationFilter.unconditional _) (s := S) fun v hv => by
    by_contra h; exact hv (hS v h)]
  rw [← Finset.prod_const]
  exact Finset.prod_le_prod₀ (fun v _ => hf0 v) fun v _ => hfM v

/-- The maximal ideals of $\mathbb Z$ of norm at most $P$ form a finite set with at most $P+1$ elements. -/
theorem exists_finset_normQ_le (P : ℕ) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 ℚ)), S.card ≤ P + 1 ∧ ∀ v, normQ v ≤ P → v ∈ S := by
  classical
  have hinj : Set.InjOn (fun v : HeightOneSpectrum (𝓞 ℚ) => Rat.HeightOneSpectrum.natGenerator v)
      {v | normQ v ≤ P} := fun v _ w _ h => eq_of_normQ_eq (by rw [normQ_rat, normQ_rat]; exact_mod_cast h)
  have hmaps : Set.MapsTo (fun v : HeightOneSpectrum (𝓞 ℚ) => Rat.HeightOneSpectrum.natGenerator v)
      {v | normQ v ≤ P} (Finset.range (P + 1) : Set ℕ) := fun v hv => by
    simp only [Set.mem_ofPred_eq, normQ_rat] at hv
    simp only [Finset.coe_range, Set.mem_Iio]
    have : Rat.HeightOneSpectrum.natGenerator v ≤ P := by exact_mod_cast hv
    omega
  have hfin : {v : HeightOneSpectrum (𝓞 ℚ) | normQ v ≤ P}.Finite :=
    Set.Finite.of_finite_image ((Finset.range (P + 1)).finite_toSet.subset (Set.mapsTo_iff_image_subset.1 hmaps))
      hinj
  refine ⟨hfin.toFinset, ?_, fun v hv => hfin.mem_toFinset.2 hv⟩
  calc hfin.toFinset.card ≤ (Finset.range (P + 1)).card :=
        Finset.card_le_card_of_injOn _ (fun v hv => by
          have := hmaps (hfin.mem_toFinset.1 hv); simpa using this) (fun v hv w hw h =>
          hinj (hfin.mem_toFinset.1 hv) (hfin.mem_toFinset.1 hw) h)
    _ = P + 1 := Finset.card_range _

/-! ### The norm of $2$ over $\mathbb Q$ -/

/-- $|2|_p^{-1}\le2$ at every prime of $\mathbb Z$, with equality only at $p = 2$. -/
theorem norm_two_inv_rat (v : HeightOneSpectrum (𝓞 ℚ)) :
    ‖(2 : v.adicCompletion ℚ)‖⁻¹ ≤ 2 ∧ (normQ v ≠ 2 → ‖(2 : v.adicCompletion ℚ)‖ = 1) := by
  by_cases h2 : ConwaySloane.Mass.pv v = 2
  · have h := ConwaySloane.Mass.norm_prime_completion v
    rw [h2] at h
    have e : (((2 : ℕ) : v.adicCompletion ℚ)) = 2 := by norm_cast
    rw [e] at h
    refine ⟨by rw [h]; norm_num, fun hne => absurd ?_ hne⟩
    rw [normQ_rat]
    have : Rat.HeightOneSpectrum.natGenerator v = 2 := h2
    rw [this]; norm_num
  · have h := ConwaySloane.Mass.norm_two_completion v h2
    exact ⟨by rw [h]; norm_num, fun _ => h⟩

/-! ### The dual index of a maximal lattice, $n$ odd -/

/-- **The dual index, $n$ odd** (from Gan–Hanke–Yu (6.6), (6.10), (6.13), `dualIndexAt_odd`): for $\mathbb Z^n$ maximal,
$[\widetilde\Lambda_p:\Lambda_p]\le2p^2$, and it is $1$ unless $p = 2$ or the Gan–Hanke–Yu mass-type at $p$ is not generic. -/
theorem dualIndexAt_odd_rat (hn : 3 ≤ n) (hodd : Odd n) (Q₀ : QuadForm (𝓞 ℚ) n) (hQ : Q₀.Nondegenerate)
    (hmax : StdIsMaximal Q₀) (v : HeightOneSpectrum (𝓞 ℚ)) :
    dualIndexAt v Q₀ ≤ 2 * normQ v ^ 2 ∧ (dualIndexAt v Q₀ ≠ 1 → normQ v = 2 ∨ oddTypeAt v Q₀ ≠ .gen) := by
  classical
  obtain ⟨-, hd⟩ := dualIndexAt_odd v hn hodd Q₀ hQ hmax
  have hq : ((LocalDensity.DVR.q (v.adicCompletionIntegers ℚ) : ℕ) : ℝ) = normQ v := DensitySD.q_eq v
  rw [hq] at hd
  obtain ⟨h2le, h2one⟩ := norm_two_inv_rat v
  have hq1 : (1 : ℝ) ≤ normQ v := by have := NFEuler.two_le_normP v; unfold normQ; exact_mod_cast (by omega : 1 ≤ _)
  set c : ℕ := if DetUnitSqAt v Q₀ then (if anisoDim v Q₀ = 1 then 0 else 2) else 1 with hc
  have hc2 : c ≤ 2 := by rw [hc]; split_ifs <;> omega
  refine ⟨?_, fun hne => ?_⟩
  · rw [hd]
    have : normQ v ^ c ≤ normQ v ^ 2 := pow_le_pow_right₀ hq1 hc2
    have h0 : 0 ≤ ‖(2 : v.adicCompletion ℚ)‖⁻¹ := inv_nonneg.2 (norm_nonneg _)
    nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ normQ v) c]
  · by_contra hcon
    push_neg at hcon
    obtain ⟨hv2, hgen⟩ := hcon
    apply hne
    rw [hd, h2one hv2, inv_one, one_mul]
    have hc0 : c = 0 := by
      unfold oddTypeAt oddTypeOf at hgen
      rw [hc]
      split_ifs at hgen ⊢ <;> simp_all
    rw [hc0, pow_zero]

/-! ### The dual index of a maximal lattice, $n$ even -/

/-- At an unramified prime where the dual index is not $1$, the even Gan–Hanke–Yu mass-type is I or II. -/
theorem evenTypeAt_of_unram (hn : 4 ≤ n) (heven : Even n) (Q₀ : QuadForm (𝓞 ℚ) n) (hQ : Q₀.Nondegenerate)
    (hmax : StdIsMaximal Q₀) {v : HeightOneSpectrum (𝓞 ℚ)} (hram : ¬ IsRamifiedAt v Q₀)
    (hne : dualIndexAt v Q₀ ≠ 1) : evenTypeAt v Q₀ = .I ∨ evenTypeAt v Q₀ = .II := by
  classical
  obtain ⟨-, h0⟩ := dualIndexAt_even_unram v hn heven Q₀ hQ hmax hram
  unfold evenTypeAt evenTypeOf
  split_ifs <;> simp_all

/-- $\lambda_{\mathrm{even},p}\ge\frac{p-1}2$ for the types I and II ($p\ge2$, $n\ge4$ even). -/
theorem lambdaEven_ge_of_I_II {p : ℝ} (hp : 2 ≤ p) (hn : 4 ≤ n) (heven : Even n) {T : EvenType}
    (hT : T = .I ∨ T = .II) : (p - 1) / 2 ≤ lambdaEven p n T := by
  obtain ⟨k, rfl⟩ := heven
  have e1 : (k + k - 2) / 2 = k - 1 := by omega
  have e2 : (k + k) / 2 = k := by omega
  have hk1 : 1 ≤ k - 1 := by omega
  have hp1 : (1 : ℝ) ≤ p := by linarith
  have ha : p ≤ p ^ (k - 1) := by simpa using pow_le_pow_right₀ hp1 hk1
  have hb : p ^ 2 ≤ p ^ k := pow_le_pow_right₀ hp1 (by omega)
  have hpp : 0 < 2 * (p + 1) := by linarith
  -- the type-I value is at least (p-1)^2/2
  have hI : (p - 1) / 2 ≤ (p ^ (k - 1) - 1) * (p ^ k - 1) / (2 * (p + 1)) := by
    rw [div_le_div_iff₀ (by norm_num) hpp]
    have h1 : p - 1 ≤ p ^ (k - 1) - 1 := by linarith
    have h2 : p ^ 2 - 1 ≤ p ^ k - 1 := by linarith
    have h3 : (p - 1) * (p ^ 2 - 1) ≤ (p ^ (k - 1) - 1) * (p ^ k - 1) :=
      mul_le_mul h1 h2 (by nlinarith) (by linarith)
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ p - 1) (by linarith : (0 : ℝ) ≤ p + 1))
      (by linarith : (0 : ℝ) ≤ p - 2)]
  rcases hT with rfl | rfl
  · simp only [lambdaEven, e1, e2]; exact hI
  · simp only [lambdaEven, e1, e2]
    refine le_trans hI (div_le_div_of_nonneg_right ?_ hpp.le)
    have h1 : 0 ≤ p ^ (k - 1) - 1 := by linarith
    have h2 : 0 ≤ p ^ k - 1 := by nlinarith
    nlinarith

/-- At a ramified prime the dual index is at most $\mathrm{Cond}(\chi)$, and so is $p$ ($n\ge4$ even, $\mathbb Z^n$
maximal). -/
theorem dualIndexAt_le_condNorm (hn : 4 ≤ n) (heven : Even n) (Q₀ : QuadForm (𝓞 ℚ) n) (hQ : Q₀.Nondegenerate)
    (hmax : StdIsMaximal Q₀) {v : HeightOneSpectrum (𝓞 ℚ)} (hram : IsRamifiedAt v Q₀) :
    dualIndexAt v Q₀ ≤ condNorm Q₀ ∧ normQ v ≤ condNorm Q₀ := by
  classical
  have h2 : ∀ w : HeightOneSpectrum (𝓞 ℚ), (2 : ℝ) ≤ normQ w := fun w => by
    have := NFEuler.two_le_normP w; unfold normQ; exact_mod_cast this
  set T := (finite_isRamifiedAt heven Q₀ hQ).toFinset
  have hvT : v ∈ T := (Set.Finite.mem_toFinset _).2 hram
  have hf := one_le_condExp hn heven Q₀ hQ hmax hram
  -- the factor at `v` is at most the whole product
  have hfac : normQ v ^ condExpAt v Q₀ ≤ condNorm Q₀ := by
    rw [condNorm_eq_prod heven Q₀ hQ, ← Finset.mul_prod_erase T _ hvT]
    have : 1 ≤ ∏ w ∈ T.erase v, normQ w ^ condExpAt w Q₀ :=
      Finset.one_le_prod₀ fun w _ => one_le_pow₀ (by linarith [h2 w])
    have h0 : 0 ≤ normQ v ^ condExpAt v Q₀ := pow_nonneg (by linarith [h2 v]) _
    nlinarith
  have hpow : normQ v ≤ normQ v ^ condExpAt v Q₀ := by
    simpa using pow_le_pow_right₀ (by linarith [h2 v] : (1 : ℝ) ≤ normQ v) hf
  refine ⟨?_, hpow.trans hfac⟩
  by_cases h2u : IsUnit (2 : v.adicCompletionIntegers ℚ)
  · rw [dualIndexAt_ram_nondyadic v hn heven Q₀ hQ hmax h2u hram, pow_one]
    exact hpow.trans hfac
  · rw [dualIndexAt_ram_dyadic v hn heven Q₀ hQ hmax h2u hram]
    exact hfac

/-- **The dual index, $n$ even**: for $\mathbb Z^n$ maximal, either $[\widetilde\Lambda_p:\Lambda_p] = 1$, or $p$ is ramified
in $\mathbb Q(\sqrt\delta)$ (dual index and $p$ at most $\mathrm{Cond}(\chi)$), or the type is I or II and the dual index is
$p^2$. -/
theorem dualIndexAt_even_rat (hn : 4 ≤ n) (heven : Even n) (Q₀ : QuadForm (𝓞 ℚ) n) (hQ : Q₀.Nondegenerate)
    (hmax : StdIsMaximal Q₀) (v : HeightOneSpectrum (𝓞 ℚ)) (hne : dualIndexAt v Q₀ ≠ 1) :
    (dualIndexAt v Q₀ ≤ condNorm Q₀ ∧ normQ v ≤ condNorm Q₀) ∨
      ((evenTypeAt v Q₀ = .I ∨ evenTypeAt v Q₀ = .II) ∧ dualIndexAt v Q₀ = normQ v ^ 2) := by
  by_cases hram : IsRamifiedAt v Q₀
  · exact Or.inl (dualIndexAt_le_condNorm hn heven Q₀ hQ hmax hram)
  · refine Or.inr ⟨evenTypeAt_of_unram hn heven Q₀ hQ hmax hram hne, ?_⟩
    obtain ⟨h1, -⟩ := dualIndexAt_even_unram v hn heven Q₀ hQ hmax hram
    exact h1.resolve_left hne

/-! ### The non-generic primes are bounded, $n$ even -/

/-- The constant $(2\pi)^r\zeta(r)/(2(r-1)!\,\zeta(2r))$ of Lemma 6.1 ($r = n/2$). -/
def lemma61Const (n : ℕ) : ℝ :=
  (2 * Real.pi) ^ (n / 2) * NFEuler.zetaR (n / 2 : ℕ) /
    (2 * (Nat.factorial (n / 2 - 1) : ℝ) * NFEuler.zetaR (2 * (n / 2 : ℕ)))

theorem lemma61Const_pos (hn : 4 ≤ n) : 0 < lemma61Const n := by
  unfold lemma61Const
  have hr : (1 : ℝ) < ((n / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < n / 2)
  have hz1 : 0 < NFEuler.zetaR (n / 2 : ℕ) := lt_of_lt_of_le one_pos (NFEuler.one_le_zetaR hr)
  have hz2 : 0 < NFEuler.zetaR (2 * ((n / 2 : ℕ) : ℝ)) := lt_of_lt_of_le one_pos
    (NFEuler.one_le_zetaR (by push_cast; linarith))
  have hf : (0 : ℝ) < Nat.factorial (n / 2 - 1) := by exact_mod_cast Nat.factorial_pos _
  have hπ := Real.pi_pos
  exact div_pos (mul_pos (pow_pos (by linarith) _) hz1) (mul_pos (mul_pos two_pos hf) hz2)

/-- **A uniform lower bound for $|L(1-\frac n2,\chi)|/2^t$** (Lemma 6.1 with $q' = 1$): for $n\ge4$ even and $\mathbb Z^n$
maximal, $|L(1-\frac n2,\chi)|/2^t > K_0(n) := 1/(2\cdot$`lemma61Const n`$)$. -/
theorem absLNeg_div_gt (hn : 4 ≤ n) (heven : Even n) (Q₀ : QuadForm (𝓞 ℚ) n) (hQ : Q₀.Nondegenerate)
    (hmax : StdIsMaximal Q₀) : 1 / (2 * lemma61Const n) < absLNeg Q₀ (n / 2) / 2 ^ numRam Q₀ := by
  have hc := lemma61Const_pos hn
  refine lemma_6_1 hn heven Q₀ hQ hmax (one_div_pos.2 (by linarith)) ∅ (by simp) (fun _ => 1) (by simp) (by simp) ?_
  rw [Finset.prod_empty]
  have e : 1 / (2 * lemma61Const n) * (2 * Real.pi) ^ (n / 2) * NFEuler.zetaR (n / 2 : ℕ) /
      (2 * (Nat.factorial (n / 2 - 1) : ℝ) * NFEuler.zetaR (2 * (n / 2 : ℕ))) = 1 / 2 := by
    rw [mul_assoc, mul_div_assoc, ← lemma61Const]
    field_simp
  rw [e]; norm_num

/-- The bound on the primes of type I or II, $n$ even: $2\epsilon B2^{\frac{n-2}2}/(K_0\prod_k|\zeta(1-2k)|) + 1$. -/
def primeBoundEven (n : ℕ) (B : ℝ) : ℝ :=
  2 * (epsilon n * B * (2 : ℝ) ^ (((n : ℝ) - 2) / 2) * (2 * lemma61Const n) / zetaProd ((n - 2) / 2)) + 1

/-- **The eligible primes are bounded, $n$ even** (Hanke 2011, proof of Thm 4.2, p. 7, with Lemmas 6.1, 7.4): if $h(L)\le B$,
every prime $p$ of Gan–Hanke–Yu mass-type I or II satisfies $p\le$ `primeBoundEven n B`, a bound depending only on $n$ and $B$. -/
@[kb "hanke2011enumerating" "Thm 4.2, proof, p. 7 (n even: finitely many eligible primes, via Lemmas 6.1 and 7.4)"]
theorem eligible_prime_bound_even (hn : 4 ≤ n) (heven : Even n) (Q₀ : QuadForm (𝓞 ℚ) n) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 ℚ) ℚ))) (hmax : StdIsMaximal Q₀) {B : ℝ}
    (hB : (Lattices.classNumber (Q₀.map (algebraMap (𝓞 ℚ) ℚ)) (stdLat ℚ n) : ℝ) ≤ B)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hT : evenTypeAt v Q₀ = .I ∨ evenTypeAt v Q₀ = .II) :
    normQ v ≤ primeBoundEven n B := by
  have h74 := lemma_7_4_even hn heven Q₀ hQ hpd hmax hB v
  have h2 : (2 : ℝ) ≤ normQ v := by have := NFEuler.two_le_normP v; unfold normQ; exact_mod_cast this
  have hge := lambdaEven_ge_of_I_II h2 hn heven hT
  have hB0 : 0 ≤ B := le_trans (Nat.cast_nonneg _) hB
  have hL := absLNeg_div_gt hn heven Q₀ hQ hmax
  have hc := lemma61Const_pos hn
  have hLp := absLNeg_pos heven Q₀ hQ (k := n / 2) (by omega)
  have hZ := zetaProd_pos ((n - 2) / 2)
  have hε : 0 < epsilon n := by unfold epsilon; split_ifs <;> norm_num
  have h2t : (0 : ℝ) < 2 ^ numRam Q₀ := by positivity
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (((n : ℝ) - 2) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  -- 2^t / |L| < 2 lemma61Const
  have hinv : 2 ^ numRam Q₀ / absLNeg Q₀ (n / 2) ≤ 2 * lemma61Const n := by
    have h1 : 1 / (2 * lemma61Const n) ≤ absLNeg Q₀ (n / 2) / 2 ^ numRam Q₀ := hL.le
    rw [div_le_div_iff₀ (by positivity) h2t] at h1
    rw [div_le_iff₀ hLp]
    linarith
  have hlam : lambdaEven (normQ v) n (evenTypeAt v Q₀) ≤
      epsilon n * B * (2 : ℝ) ^ (((n : ℝ) - 2) / 2) * (2 * lemma61Const n) / zetaProd ((n - 2) / 2) := by
    calc lambdaEven (normQ v) n (evenTypeAt v Q₀) ≤ epsilon n * 2 ^ numRam Q₀ * B * bEven Q₀ := h74
      _ = epsilon n * B * (2 : ℝ) ^ (((n : ℝ) - 2) / 2) * (2 ^ numRam Q₀ / absLNeg Q₀ (n / 2)) /
          zetaProd ((n - 2) / 2) := by unfold bEven; field_simp
      _ ≤ _ := by
        refine div_le_div_of_nonneg_right ?_ hZ.le
        exact mul_le_mul_of_nonneg_left hinv (by positivity)
  unfold primeBoundEven
  linarith

/-! ### The determinant bound -/

/-- $|\det H| = \prod_p[\widetilde\Lambda_p:\Lambda_p]$ over $\mathbb Z$ (product formula). -/
theorem tprod_dualIndexAt_rat (Q₀ : QuadForm (𝓞 ℚ) n) (hQ : Q₀.Nondegenerate) :
    ∏' v : HeightOneSpectrum (𝓞 ℚ), dualIndexAt v Q₀ = |algebraMap (𝓞 ℚ) ℚ Q₀.hessian.det| := by
  rw [tprod_dualIndexAt Q₀ hQ, Fintype.prod_unique, Rat.infinitePlace_apply]
  have : (default : InfinitePlace ℚ).mult = 1 := by
    rw [InfinitePlace.mult, if_pos (by rw [Subsingleton.elim default Rat.infinitePlace]; exact Rat.isReal_infinitePlace)]
  rw [this, pow_one]

/-- **The determinant bound** (the step of Hanke 2011, proof of Thm 4.2, p. 7, made explicit): for $n\ge3$ and $B$ there is
$D$ such that every non-degenerate positive definite $Q_0$ over $\mathbb Z$ in $n$ variables with $\mathbb Z^n$ maximal and
$h\le B$ has $|\det H_{Q_0}|\le D$. -/
@[kb "hanke2011enumerating" "Theorem 4.2, proof, p. 7 (bounded local data; here: bounded Hessian determinant)"]
theorem abs_det_le (hn : 3 ≤ n) (B : ℝ) :
    ∃ D : ℕ, ∀ Q₀ : QuadForm (𝓞 ℚ) n, Q₀.Nondegenerate → IsTotallyPosDef (Q₀.map (algebraMap (𝓞 ℚ) ℚ)) →
      StdIsMaximal Q₀ → (Lattices.classNumber (Q₀.map (algebraMap (𝓞 ℚ) ℚ)) (stdLat ℚ n) : ℝ) ≤ B →
      |algebraMap (𝓞 ℚ) ℚ Q₀.hessian.det| ≤ D := by
  classical
  -- a uniform prime bound `P` and a uniform factor bound `M`
  obtain ⟨P, M, hM1, hPM⟩ : ∃ (P : ℕ) (M : ℝ), 1 ≤ M ∧ ∀ Q₀ : QuadForm (𝓞 ℚ) n, Q₀.Nondegenerate →
      IsTotallyPosDef (Q₀.map (algebraMap (𝓞 ℚ) ℚ)) → StdIsMaximal Q₀ →
      (Lattices.classNumber (Q₀.map (algebraMap (𝓞 ℚ) ℚ)) (stdLat ℚ n) : ℝ) ≤ B →
      ∀ v, dualIndexAt v Q₀ ≤ M ∧ (dualIndexAt v Q₀ ≠ 1 → normQ v ≤ P) := by
    rcases Nat.even_or_odd n with heven | hodd
    · have hn4 : 4 ≤ n := by obtain ⟨k, rfl⟩ := heven; omega
      obtain ⟨C, hC⟩ := lemma_7_3_finite hn4 heven B
      set X : ℝ := max C (primeBoundEven n B)
      refine ⟨⌈X⌉₊, max (max C 1) (X ^ 2), le_max_of_le_left (le_max_right _ _),
        fun Q₀ hQ hpd hmax hB v => ?_⟩
      have hCQ := hC Q₀ hQ hpd hmax hB
      by_cases h1 : dualIndexAt v Q₀ = 1
      · exact ⟨by rw [h1]; exact le_max_of_le_left (le_max_right _ _), fun h => absurd h1 h⟩
      · rcases dualIndexAt_even_rat hn4 heven Q₀ hQ hmax v h1 with ⟨hd, hp⟩ | ⟨hT, hd⟩
        · refine ⟨le_max_of_le_left (le_max_of_le_left (hd.trans hCQ)), fun _ => ?_⟩
          exact (hp.trans (hCQ.trans (le_max_left _ _))).trans (Nat.le_ceil _)
        · have hp := eligible_prime_bound_even hn4 heven Q₀ hQ hpd hmax hB v hT
          have hpX : normQ v ≤ X := hp.trans (le_max_right _ _)
          have h0 : 0 ≤ normQ v := by have := NFEuler.two_le_normP v; unfold normQ; positivity
          refine ⟨?_, fun _ => hpX.trans (Nat.le_ceil _)⟩
          rw [hd]
          exact le_max_of_le_right (pow_le_pow_left₀ h0 hpX 2)
    · set X : ℝ := max 2 (2 * epsilon n * B * bOdd n + 1)
      refine ⟨⌈X⌉₊, 2 * X ^ 2, ?_, fun Q₀ hQ hpd hmax hB v => ?_⟩
      · have : (2 : ℝ) ≤ X := le_max_left _ _
        nlinarith
      obtain ⟨hle, himp⟩ := dualIndexAt_odd_rat hn hodd Q₀ hQ hmax v
      have h0 : 0 ≤ normQ v := by have := NFEuler.two_le_normP v; unfold normQ; positivity
      have hpX : dualIndexAt v Q₀ ≠ 1 → normQ v ≤ X := fun h => by
        rcases himp h with h2 | hg
        · rw [h2]; exact le_max_left _ _
        · exact (eligible_prime_bound_odd hn hodd Q₀ hQ hpd hmax hB v hg).trans (le_max_right _ _)
      refine ⟨?_, fun h => (hpX h).trans (Nat.le_ceil _)⟩
      by_cases h1 : dualIndexAt v Q₀ = 1
      · rw [h1]
        have : (2 : ℝ) ≤ X := le_max_left _ _
        nlinarith
      · exact hle.trans (by nlinarith [pow_le_pow_left₀ h0 (hpX h1) 2])
  obtain ⟨S, hS, hSP⟩ := exists_finset_normQ_le P
  refine ⟨⌈M ^ (P + 1)⌉₊, fun Q₀ hQ hpd hmax hB => ?_⟩
  have hb := hPM Q₀ hQ hpd hmax hB
  suffices h : ((|algebraMap (𝓞 ℚ) ℚ Q₀.hessian.det| : ℚ) : ℝ) ≤ (⌈M ^ (P + 1)⌉₊ : ℕ) by exact_mod_cast h
  rw [← tprod_dualIndexAt_rat Q₀ hQ]
  calc ∏' v, dualIndexAt v Q₀ ≤ M ^ S.card :=
        tprod_le_pow_card S (fun v hv => hSP v ((hb v).2 hv))
          (fun v => (dualIndexAt_pos v Q₀ hQ).le) fun v => (hb v).1
    _ ≤ M ^ (P + 1) := pow_le_pow_right₀ hM1 hS
    _ ≤ _ := Nat.le_ceil _

/-! ### Theorem 4.2 -/

open Tamagawa.RatBridge in
/-- **Theorem 4.2** (Hanke 2011, p. 7): *there are only finitely many (classes of) maximal $\mathbb Z$-valued quadratic
lattices in $n\ge3$ variables with a priori bounded class number.* For every $n\ge3$ and $B$ there is a finite list $S$ of
forms over $\mathcal O_{\mathbb Q} = \mathbb Z$ such that every non-degenerate positive definite $Q_0$ with $\mathbb Z^n$
maximal and $h(\mathbb Z^n)\le B$ is $\mathbb Z$-equivalent (`IsometricIn (𝓞 ℚ)`) to a member of $S$. **Unconditional.**
*Proof:* the determinant bound `abs_det_le` and Hermite's reduction (`Siegel.exists_intEquiv_hessian_bounded`). -/
@[kb "hanke2011enumerating" "Theorem 4.2, p. 7"]
theorem theorem_4_2 : Theorem42 := by
  classical
  refine ⟨fun n hn B => ?_⟩
  obtain ⟨D, hD⟩ := abs_det_le hn B
  -- the finitely many integral forms with Hessian entries bounded by `E_n(d)`, `|d| ≤ D`
  set T : Set (QuadForm ℤ n) := ⋃ d ∈ Finset.Icc (-(D : ℤ)) D,
    {Q' : QuadForm ℤ n | ∀ i j, |Q'.hessian i j| ≤ Siegel.Hermite.entryBound n d}
  have hT : T.Finite := Set.Finite.biUnion (Finset.finite_toSet _) fun d _ =>
    Siegel.finite_setOf_hessian_bounded _
  refine ⟨hT.toFinset.image up, fun Q₀ hQ hpd hmax hB => ?_⟩
  have hpdZ : IntQF.PosDef (down Q₀) := posDef_down hpd
  obtain ⟨Q', he, hb⟩ := Siegel.exists_intEquiv_hessian_bounded hpdZ
  -- the determinant of `down Q₀` is bounded by `D`
  have hdet : (down Q₀).hessian.det = eZ Q₀.hessian.det := by
    rw [Siegel.hessian_map]; exact (RingHom.map_det _ _).symm
  have hDQ := hD Q₀ hQ hpd hmax hB
  rw [← Rat.ringOfIntegersEquiv_apply_coe] at hDQ
  have hdD : (down Q₀).hessian.det ∈ Finset.Icc (-(D : ℤ)) D := by
    rw [hdet, Finset.mem_Icc, ← abs_le]
    exact_mod_cast hDQ
  have hQ'T : Q' ∈ T := Set.mem_biUnion hdD hb
  refine ⟨up Q', Finset.mem_image.2 ⟨Q', hT.mem_toFinset.2 hQ'T, rfl⟩, ?_⟩
  -- transport the equivalence back to `𝓞 ℚ`
  have hGL : Siegel.IsometricGL (up (down Q₀)) (up Q') := isometricGL_map_hom _ he
  rw [up_down] at hGL
  obtain ⟨g, hg⟩ := hGL
  refine ⟨g.val, (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit, fun x => ?_⟩
  exact hg x

end QuadFormsKB.Hanke2011Enumerating
