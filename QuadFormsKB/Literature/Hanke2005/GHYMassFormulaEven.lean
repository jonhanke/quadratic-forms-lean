/-
# The Gan–Hanke–Yu mass formula for special orthogonal groups, even rank (GHY 2001, Proposition 7.5)

W. T. Gan, J. Hanke, J.-K. Yu, *On an exact mass formula of Shimura*, Duke Math. J. 107 (2001), §7 ((7.1)–(7.3),
Prop. 7.5, p. 119), Lemma A.1(iv) (p. 123); J. Hanke, *An exact mass formula for quadratic forms over number fields*,
J. Reine Angew. Math. 584 (2005), Theorem 5.1.

Let $k$ (= `F`) be totally real of degree $d$, $V$ totally definite of even rank $m = 2n\ge4$ (GHY's $n$ = `n / 2`),
$\delta$ the discriminant, $L = k(\sqrt\delta)$, $\chi$ its quadratic character, $\Lambda = \mathcal O_k^m$ maximal. GHY:
$$\mathrm{Mass}(\Lambda) = \Big(\frac1{2^{nd}}L(M)\,\tau(G)\Big)\prod_{v\in S}\lambda_v,\qquad
L(M) = \prod_{r=1}^{n-1}\zeta_k(1-2r)\cdot L(1-n,\chi),\qquad\tau(G) = 2,$$
$$\lambda_v = \frac{(q^{n-1}-1)(q^n-1)}{2(q+1)}\ (\delta\in k_v^{\times2},\ w = -1),\quad
\frac{(q^{n-1}+1)(q^n+1)}{2(q+1)}\ (\delta\notin k_v^{\times2},\ E_\delta\ \text{unramified},\ w = -1),\quad
\frac12\ (E_\delta\ \text{ramified}),$$
and $\lambda_v = 1$ otherwise. **Formalized** as `ghy_prop75`, conditional on one named input:

* `RamifiedDualIndexConductor`: at a place ramified in $E_\delta$, $[\widetilde\Lambda_v:\Lambda_v] = q_v^{f_v}$, $f_v$ the conductor
  exponent of $k_v(\sqrt\delta)/k_v$ (`condExp`, defined by norm groups: the least $c$ with $U^{(c)}\subseteq N(E_v^\times)$; GHY
  Lemma A.1(iv): $f_v = d$, the exponent of the different, and $[\widetilde\Lambda_v:\Lambda_v] = |\mathrm{disc}\,A_{E_\delta}|^{-1} = q^d$).

Readings (as for Prop. 7.4, `GHYMassFormula.lean`): $L(M)$ is read as $|L(M)|$; $|\zeta_k(1-2r)|$ and
$|L(1-n,\chi)| = (|D_k|\,N\mathfrak f_\chi)^{n-1/2}\big(2(n-1)!/(2\pi)^n\big)^dL(n,\chi)$ are written through the functional
equations (Mathlib has no analytic continuation), with $N\mathfrak f_\chi = \prod_{v\ \text{ramified}}q_v^{f_v}$ (`condNorm`); $w = -1$
is read as $t_v = 4$ for $\delta$ a square and as $[\widetilde\Lambda_v:\Lambda_v]\ne1$ for $E_\delta$ unramified (the lattices
$\Delta^{n-2}\perp A_D$ and $\Delta^{n-1}\perp\pi A_{E_\delta}$ of GHY (6.5)).

*Proof.* `theorem51_definite_general` (for even rank $\lambda'_v = \lambda_v$) and the placewise identity
$\lambda^{\rm GHY}_v\,(q_v^{f_v})^{n-1/2} = [\widetilde\Lambda_v:\Lambda_v]^{n-1/2}\lambda_v$ (`lambdaGHYEvenAt_mul`; the factor $q^{f_v}$ only at
ramified places), from the dual index at the unramified places (`dualIndexAt_even_unram`) and the input.
-/
import QuadFormsKB.Literature.Hanke2005.GHYEvenDual
import QuadFormsKB.Literature.Hanke2005.GHYMassFormula

open NumberField IsDedekindDomain Real
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.deprecated false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil
  QuadFormsKB.Tamagawa.Indefinite QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR QuadFormsKB.Tamagawa.LatChange

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-! ### The conductor -/

section Conductor

variable (v : HeightOneSpectrum (𝓞 F))

open Classical in
/-- **The conductor exponent $f_v$ of $F_v(\sqrt x)/F_v$** (GHY 2001, Lemma A.1(iv), p. 123; Serre, *Local Fields*, Ch. XV,
§2): the least $c$ such that every unit $u\equiv1 \bmod \pi^c$ is a norm from $F_v(\sqrt x)$, i.e. has Hilbert symbol
$(x,u)_v = 1$ (and $0$ if there is no such $c$, which does not happen for $x\ne0$, by the local square theorem). -/
@[kb "ganhankeyu2001" "Lemma A.1(iv), p. 123 (U^i ⊆ N E^× iff i ≥ d: the conductor of E/F)"]
def condExp (x : v.adicCompletion F) : ℕ :=
  if h : ∃ c : ℕ, ∀ u : v.adicCompletionIntegers F, IsUnit u → NF.π v ^ c ∣ u - 1 →
      hilbertSymbol (v.adicCompletion F) x (u : v.adicCompletion F) = 1 then Nat.find h else 0

open Classical in
/-- The local factor $N\mathfrak f_{\chi,v} = q_v^{f_v}$ of the norm of the conductor of $\chi$ ($1$ at unramified places). -/
def condFactor (Q₀ : QuadForm (𝓞 F) n) : ℝ :=
  if IsRamifiedAt v Q₀ then (normQ v) ^ condExp v (algebraMap F (v.adicCompletion F) (discK Q₀)) else 1

end Conductor

/-- **$N\mathfrak f_\chi$**, the norm of the conductor of the quadratic character $\chi$ of $F(\sqrt\delta)/F$:
$\prod_vq_v^{f_v}$ over the places ramified in $F(\sqrt\delta)$. -/
def condNorm (Q₀ : QuadForm (𝓞 F) n) : ℝ := ∏' v : HeightOneSpectrum (𝓞 F), condFactor v Q₀

/-- **The dual index at a ramified place is the norm of the local conductor** (a **named input**; GHY 2001, Lemma A.1(iv),
(6.5), (6.13): the maximal lattice is $\Delta^{n-1}\perp A_{E_\delta}$ with $A_{E_\delta}$ the scaled norm form of the ring of integers,
whose discriminant has valuation $d$ = the exponent of the different = the conductor exponent $f_v$). For even $n\ge4$,
$Q_0$ nondegenerate with $\mathcal O_F^n$ maximal, and $v$ ramified in $F(\sqrt\delta)$:
$[\widetilde\Lambda_v:\Lambda_v] = q_v^{f_v}$. Field: `dual_eq`. Not the conclusion of Prop. 7.5: a statement about one
local index. -/
@[kb "ganhankeyu2001" "Lemma A.1(iv), p. 123; (6.5), (6.13) (dual index of A_{E_δ} = norm of the conductor)"]
structure RamifiedDualIndexConductor (F : Type) [Field F] [NumberField F] : Prop where
  /-- $[\widetilde\Lambda_v:\Lambda_v] = q_v^{f_v}$ at a ramified place. -/
  dual_eq : ∀ {n : ℕ}, 4 ≤ n → Even n → ∀ Q₀ : QuadForm (𝓞 F) n, Q₀.Nondegenerate → StdIsMaximal Q₀ →
    ∀ v : HeightOneSpectrum (𝓞 F), IsRamifiedAt v Q₀ →
      dualIndexAt v Q₀ = (normQ v) ^ condExp v (algebraMap F (v.adicCompletion F) (discK Q₀))

/-! ### GHY's local factor, even rank -/

open Classical in
/-- **GHY's $\lambda_v$ for even rank $m = 2k$** (GHY 2001, Proposition 7.5, p. 119; Table 3), as a function of $q$, $k$,
$t = t_v$, whether $\delta$ is a square (`sq`), whether $E_\delta$ is ramified (`ram`) and whether the lattice is self-dual
(`sd`; for $E_\delta$ unramified, $w = 1$ iff self-dual). -/
@[kb "ganhankeyu2001" "Proposition 7.5, p. 119 (λ_v, even rank)"]
def lambdaGHYEven (q : ℝ) (k t : ℕ) (sq ram sd : Prop) : ℝ :=
  if sq then (if t = 0 then 1 else (q ^ (k - 1) - 1) * (q ^ k - 1) / (2 * (q + 1)))
  else if ram then 1 / 2
  else if sd then 1 else (q ^ (k - 1) + 1) * (q ^ k + 1) / (2 * (q + 1))

/-- GHY's $\lambda_v$ at a finite place for $Q_0$ of even rank. -/
def lambdaGHYEvenAt (v : HeightOneSpectrum (𝓞 F)) (Q₀ : QuadForm (𝓞 F) n) : ℝ :=
  lambdaGHYEven (normQ v) (n / 2) (anisoDim v Q₀) (IsSquare (algebraMap F (v.adicCompletion F) (discK Q₀)))
    (IsRamifiedAt v Q₀) (dualIndexAt v Q₀ = 1)

theorem not_isSquare_of_isRamifiedAt (v : HeightOneSpectrum (𝓞 F)) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (h : IsRamifiedAt v Q₀) : ¬ IsSquare (algebraMap F (v.adicCompletion F) (discK Q₀)) := by
  rintro ⟨s, hs⟩
  apply h
  have hd : discK Q₀ ≠ 0 := by
    unfold discK
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (hessian_det_F_ne_zero Q₀ hQ)
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hs
    exact hd ((map_eq_zero_iff _ (algebraMap F (v.adicCompletion F)).injective).mp hs)
  refine ⟨s⁻¹, inv_ne_zero hs0, 0, by simp, ?_⟩
  rw [hs]; field_simp; simp

/-- $(q^2)^{k-1/2} = q^{2k}/q$. -/
theorem sq_rpow_half {q : ℝ} (hq : 0 < q) (k : ℕ) : (q ^ 2) ^ ((k : ℝ) - 1 / 2) = q ^ (2 * k) / q := by
  rw [Real.rpow_sub (by positivity), Real.rpow_natCast, ← pow_mul, mul_comm 2 k]
  congr 1
  rw [← Real.rpow_natCast q 2, ← Real.rpow_mul hq.le]
  norm_num

/-- **GHY's even-rank $\lambda_v$ against Hanke's** (placewise): $\lambda^{\rm GHY}_v\,(N\mathfrak f_{\chi,v})^{k-1/2} =
[\widetilde\Lambda_v:\Lambda_v]^{k-1/2}\,\lambda_v$, $k = n/2$. -/
theorem lambdaGHYEvenAt_mul (I : RamifiedDualIndexConductor F) (v : HeightOneSpectrum (𝓞 F)) (hn : 4 ≤ n)
    (heven : Even n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hmax : StdIsMaximal Q₀) :
    lambdaGHYEvenAt v Q₀ * condFactor v Q₀ ^ (((n / 2 : ℕ) : ℝ) - 1 / 2) =
      dualIndexAt v Q₀ ^ (((n / 2 : ℕ) : ℝ) - 1 / 2) * lambdaAt v Q₀ := by
  classical
  have hq1 : 1 < normQ v := one_lt_normQ v
  have hq0 : 0 < normQ v := lt_trans zero_lt_one hq1
  have hk2 : 2 ≤ n / 2 := by omega
  have hiff := anisoDim_eq_two_iff v Q₀ hQ heven
  have hw := two_mul_wittIndex_le v Q₀ hQ
  have hpar : anisoDim v Q₀ % 2 = 0 := by
    unfold anisoDim; obtain ⟨r, hr⟩ := heven; omega
  have ht4 : anisoDim v Q₀ ≤ 4 := anisoDim_le_four v Q₀ hQ
  have hsd := (shimuraMaximalTypes (F := F)).selfDual (by omega) Q₀ hQ hmax v
  set k := n / 2 with hk
  set q := normQ v with hqdef
  have hm : (n / 2 : ℕ) = k := rfl
  -- `q ^ (-k)` and `q ^ (1 - k)` through `X = q ^ k`
  have hA : q ^ (-((k : ℕ) : ℝ)) = (q ^ k)⁻¹ := by rw [Real.rpow_neg hq0.le, Real.rpow_natCast]
  have hB : q ^ (1 - ((k : ℕ) : ℝ)) = q * (q ^ k)⁻¹ := by
    rw [sub_eq_add_neg, Real.rpow_add hq0, Real.rpow_one, hA]
  have hA2 : q ^ (-(2 * ((k : ℕ) : ℝ))) = ((q ^ k) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hq0.le, show 2 * ((k : ℕ) : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
      pow_mul, ← pow_mul, mul_comm, pow_mul]
  have hkq : q ^ (k - 1) = q ^ k / q := by
    rw [eq_div_iff hq0.ne', ← pow_succ, Nat.sub_add_cancel (by omega)]
  have hX : 0 < q ^ k := pow_pos hq0 k
  by_cases hr : IsRamifiedAt v Q₀
  · have hsq := not_isSquare_of_isRamifiedAt v Q₀ hQ hr
    have ht : anisoDim v Q₀ = 2 := hiff.2 hsq
    have hd := I.dual_eq hn heven Q₀ hQ hmax v hr
    have hd1 : dualIndexAt v Q₀ ≠ 1 := fun h1 =>
      (not_isRamifiedAt_of_dualIndexAt_eq_one v Q₀ heven h1) hr
    unfold lambdaGHYEvenAt lambdaGHYEven condFactor lambdaAt lambdaHanke
    rw [if_neg hsq, if_pos hr, if_pos hr, if_neg hd1, ht, hd]
    simp only [hr, ite_true]
    ring
  · have hc : condFactor v Q₀ = 1 := by unfold condFactor; rw [if_neg hr]
    rw [hc, Real.one_rpow, mul_one]
    obtain ⟨hE1, hE2⟩ := dualIndexAt_even_unram v hn heven Q₀ hQ hmax hr
    by_cases hsq : IsSquare (algebraMap F (v.adicCompletion F) (discK Q₀))
    · have ht2 : anisoDim v Q₀ ≠ 2 := fun h => (hiff.1 h) hsq
      rcases (by omega : anisoDim v Q₀ = 0 ∨ anisoDim v Q₀ = 4) with ht | ht
      · have h1 := hE2 ht
        unfold lambdaGHYEvenAt lambdaGHYEven
        rw [if_pos hsq, if_pos ht, h1, Real.one_rpow, one_mul, lambdaAt_eq_one_of Q₀ v h1]
      · have hd1 : dualIndexAt v Q₀ ≠ 1 := fun h1 => by have := (hsd h1).1; omega
        have hd2 : dualIndexAt v Q₀ = q ^ 2 := hE1.resolve_left hd1
        unfold lambdaGHYEvenAt lambdaGHYEven lambdaAt lambdaHanke
        rw [if_pos hsq, if_neg (by omega), if_neg hd1, ht, hd2, sq_rpow_half hq0, hkq]
        simp only
        rw [hm, hB, hA]
        rw [pow_mul]
        field_simp
        ring
    · have ht : anisoDim v Q₀ = 2 := hiff.2 hsq
      by_cases hsd1 : dualIndexAt v Q₀ = 1
      · unfold lambdaGHYEvenAt lambdaGHYEven
        rw [if_neg hsq, if_neg hr, if_pos hsd1, hsd1, Real.one_rpow, one_mul, lambdaAt_eq_one_of Q₀ v hsd1]
      · have hd2 : dualIndexAt v Q₀ = q ^ 2 := hE1.resolve_left hsd1
        unfold lambdaGHYEvenAt lambdaGHYEven lambdaAt lambdaHanke
        rw [if_neg hsq, if_neg hr, if_neg hsd1, if_neg hsd1, ht, hd2, sq_rpow_half hq0, hkq]
        simp only [hr, ite_false]
        rw [hm, hB, hA]
        rw [pow_mul]
        field_simp
        ring

/-! ### The global formula -/

theorem condFactor_pos (v : HeightOneSpectrum (𝓞 F)) (Q₀ : QuadForm (𝓞 F) n) : 0 < condFactor v Q₀ := by
  unfold condFactor
  split_ifs
  · exact pow_pos (lt_trans zero_lt_one (one_lt_normQ v)) _
  · exact one_pos

/-- **The product of GHY's even-rank local factors:** $\prod_v\lambda^{\rm GHY}_v\cdot(N\mathfrak f_\chi)^{k-1/2} =
[\widetilde\Lambda:\Lambda]^{k-1/2}\prod_v\lambda_v$. -/
theorem tprod_lambdaGHYEvenAt (I : RamifiedDualIndexConductor F) (hn : 4 ≤ n) (heven : Even n) (Q₀ : QuadForm (𝓞 F) n)
    (hQ : Q₀.Nondegenerate) (hmax : StdIsMaximal Q₀) :
    (∏' v : HeightOneSpectrum (𝓞 F), lambdaGHYEvenAt v Q₀) * condNorm Q₀ ^ (((n / 2 : ℕ) : ℝ) - 1 / 2) =
      (∏' v, dualIndexAt v Q₀) ^ (((n / 2 : ℕ) : ℝ) - 1 / 2) * ∏' v, lambdaAt v Q₀ := by
  set S := (hasFiniteMulSupport_dualIndexAt Q₀ hQ).toFinset with hS
  have hoff : ∀ v ∉ S, dualIndexAt v Q₀ = 1 := fun v hv => by
    by_contra h
    exact hv ((Set.Finite.mem_toFinset _).mpr h)
  have hc1 : ∀ v ∉ S, condFactor v Q₀ = 1 := fun v hv => by
    unfold condFactor
    rw [if_neg (not_isRamifiedAt_of_dualIndexAt_eq_one v Q₀ heven (hoff v hv))]
  have hl1 : ∀ v ∉ S, lambdaAt v Q₀ = 1 := fun v hv => lambdaAt_eq_one_of Q₀ v (hoff v hv)
  have hg1 : ∀ v ∉ S, lambdaGHYEvenAt v Q₀ = 1 := fun v hv => by
    have h := lambdaGHYEvenAt_mul I v hn heven Q₀ hQ hmax
    rw [hc1 v hv, hoff v hv, hl1 v hv] at h
    simpa using h
  unfold condNorm
  rw [tprod_eq_prod (L := SummationFilter.unconditional _) hg1, tprod_eq_prod (L := SummationFilter.unconditional _) hc1,
    tprod_eq_prod (L := SummationFilter.unconditional _) hoff, tprod_eq_prod (L := SummationFilter.unconditional _) hl1,
    ← Real.finsetProd_rpow S _ (fun v _ => (condFactor_pos v Q₀).le),
    ← Real.finsetProd_rpow S _ (fun v _ => (dualIndexAt_pos v Q₀ hQ).le),
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun v _ => lambdaGHYEvenAt_mul I v hn heven Q₀ hQ hmax

/-- **$|L(1-n,\chi)|$ through the functional equation** ($F$ totally real of degree $d$, $\chi$ the quadratic character of
$F(\sqrt\delta)$, $n\ge1$): $(|D_F|\,N\mathfrak f_\chi)^{n-1/2}\big(2(n-1)!/(2\pi)^n\big)^dL(n,\chi)$. -/
@[kb "ganhankeyu2001" "(7.2) (L(1 − n, χ), through the functional equation of the Hecke L-function)"]
def absLNeg (Q₀ : QuadForm (𝓞 F) n) (k : ℕ) : ℝ :=
  (|(discr F : ℝ)| * condNorm Q₀) ^ ((k : ℝ) - 1 / 2) *
    (2 * (Nat.factorial (k - 1) : ℝ) / (2 * π) ^ k) ^ Module.finrank ℚ F *
      NFEuler.LFunctionNF (fun v => chiK v Q₀) (k : ℝ)

/-- **GHY's $|L(M)|$ for even rank $2k$** (GHY 2001, (7.2)): $\prod_{r=1}^{k-1}|\zeta_F(1-2r)|\cdot|L(1-k,\chi)|$. -/
@[kb "ganhankeyu2001" "(7.2) (L(M) for m = 2n, in absolute value)"]
def lMotiveEven (Q₀ : QuadForm (𝓞 F) n) (k : ℕ) : ℝ := lMotiveOdd F (k - 1) * absLNeg Q₀ k

/-- **GHY 2001, Proposition 7.5** (even rank $m = 2k\ge4$; totally real $F$ of degree $d$; $V$ totally definite;
$\Lambda = \mathcal O_F^m$ maximal): $\mathrm{Mass}(\Lambda) = \big(2^{-kd}\,|L(M)|\,\tau(G)\big)\prod_v\lambda_v$, $\tau(G) = 2$, with
GHY's $\lambda_v$ (`lambdaGHYEvenAt`). **Conditional** on the named input `RamifiedDualIndexConductor F` (the dual index at
a ramified place is the norm of the local conductor). -/
@[kb "ganhankeyu2001" "Proposition 7.5, p. 119 (with (7.1)–(7.3))"]
theorem ghy_prop75 [IsTotallyReal F] (I : RamifiedDualIndexConductor F) (hn : 4 ≤ n) (heven : Even n)
    (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (hmax : StdIsMaximal Q₀) :
    ∑' i : DC Q₀, ((Nat.card (unitGroup Q₀ i) : ℝ≥0∞))⁻¹ =
      ENNReal.ofReal (((2 : ℝ) ^ ((n / 2) * Module.finrank ℚ F))⁻¹ * lMotiveEven Q₀ (n / 2) * 2 *
        ∏' v : HeightOneSpectrum (𝓞 F), lambdaGHYEvenAt v Q₀) := by
  classical
  rw [theorem51_definite_general (by omega) Q₀ hQ hpd hmax]
  congr 1
  have hodd : ¬ Odd n := Nat.not_odd_iff_even.mpr heven
  have hgen : (∏' v : HeightOneSpectrum (𝓞 F), lambdaGen v Q₀) = ∏' v, lambdaAt v Q₀ :=
    tprod_congr fun v => by unfold lambdaGen; rw [if_neg (fun h => hodd h.1)]
  have hT := tprod_lambdaGHYEvenAt I hn heven Q₀ hQ hmax
  have hNpos : 0 < condNorm Q₀ := by
    unfold condNorm
    set S := (hasFiniteMulSupport_dualIndexAt Q₀ hQ).toFinset
    rw [tprod_eq_prod (L := SummationFilter.unconditional _) (s := S) fun v hv => by
      unfold condFactor
      rw [if_neg (not_isRamifiedAt_of_dualIndexAt_eq_one v Q₀ heven (by
        by_contra h; exact hv ((Set.Finite.mem_toFinset _).mpr h)))]]
    exact Finset.prod_pos fun v _ => condFactor_pos v Q₀
  unfold theorem51RHSGen
  dsimp only
  have hB : (∏ w : {w : InfinitePlace F // w.IsReal}, bPhi n (rAt Q₀ w)) = 1 :=
    Finset.prod_eq_one fun w _ => by rw [rAt_eq_zero Q₀ hQ hpd w.1, bPhi_zero]
  have hC : InfinitePlace.nrComplexPlaces F = 0 := IsTotallyReal.nrComplexPlaces_eq_zero F
  rw [hB, hC, pow_zero, if_neg hodd, hgen]
  obtain ⟨r, rfl⟩ := heven
  obtain ⟨j, rfl⟩ : ∃ j, r = j + 2 := ⟨r - 2, by omega⟩
  have e1 : (j + 2 + (j + 2) - 1) ^ 2 / 4 = (j + 1) * (j + 2) := by
    rw [show j + 2 + (j + 2) - 1 = 2 * j + 3 by omega,
      show (2 * j + 3) ^ 2 = 4 * ((j + 1) * (j + 2)) + 1 by ring]; omega
  have e2 : (j + 2 + (j + 2) - 1) / 2 = j + 1 := by omega
  have e3 : (j + 2 + (j + 2)) / 2 = j + 2 := by omega
  have e4 : (j + 2 + (j + 2)) / 2 - 1 = j + 1 := by omega
  have e5 : j + 2 - 1 = j + 1 := by omega
  simp only [e1, e2, e3] at hT ⊢
  unfold lMotiveEven absLNeg
  rw [e5, lMotiveOdd_eq]
  have hD : 0 < |(discr F : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero F)
  have hI : 0 < ∏' v, dualIndexAt v Q₀ := tprod_dualIndexAt_pos Q₀ hQ
  -- exponents
  have fs : ((((j + 2 + (j + 2) : ℕ) : ℝ) - 1) / 2) = (((j + 2 : ℕ) : ℝ) - 1 / 2) := by push_cast; ring
  have fL : (((j + 2 + (j + 2) : ℕ) : ℝ) / 2) = ((j + 2 : ℕ) : ℝ) := by push_cast; ring
  have fπ : (2 * π) ^ (-((j + 2 : ℕ) : ℝ)) = ((2 * π) ^ (j + 2))⁻¹ := by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  have fD : |(discr F : ℝ)| ^ ((j + 1) * (j + 2)) * |(discr F : ℝ)| ^ (1 / 2 : ℝ) =
      |(discr F : ℝ)| ^ ((j + 1) ^ 2) * |(discr F : ℝ)| ^ (((j + 2 : ℕ) : ℝ) - 1 / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast _ ((j + 1) ^ 2), ← Real.rpow_add hD, ← Real.rpow_add hD]
    congr 1; push_cast; ring
  rw [fs, fL, fπ]
  rw [Real.mul_rpow hD.le hNpos.le]
  -- isolate `∏ λ^GHY` from `hT`
  have hT' : (∏' v : HeightOneSpectrum (𝓞 F), lambdaGHYEvenAt v Q₀) =
      (∏' v, dualIndexAt v Q₀) ^ (((j + 2 : ℕ) : ℝ) - 1 / 2) * (∏' v, lambdaAt v Q₀) /
        condNorm Q₀ ^ (((j + 2 : ℕ) : ℝ) - 1 / 2) := by
    rw [eq_div_iff (Real.rpow_pos_of_pos hNpos _).ne']; exact hT
  rw [hT']
  have hNs : 0 < condNorm Q₀ ^ (((j + 2 : ℕ) : ℝ) - 1 / 2) := Real.rpow_pos_of_pos hNpos _
  rw [show (2 : ℝ) ^ ((j + 1) * Module.finrank ℚ F) = (2 : ℝ) ^ ((j + 2) * Module.finrank ℚ F) / 2 ^ Module.finrank ℚ F by
    rw [eq_div_iff (by positivity), ← pow_add]; congr 1; ring]
  have hC2 : 0 < |(discr F : ℝ)| ^ ((j + 1) ^ 2) := by positivity
  have fE : |(discr F : ℝ)| ^ (((j + 2 : ℕ) : ℝ) - 1 / 2) =
      |(discr F : ℝ)| ^ ((j + 1) * (j + 2)) * |(discr F : ℝ)| ^ (1 / 2 : ℝ) / |(discr F : ℝ)| ^ ((j + 1) ^ 2) := by
    rw [fD]; field_simp
  rw [fE, mul_div_assoc (2 : ℝ) ((Nat.factorial (j + 1) : ℕ) : ℝ) ((2 * π) ^ (j + 2)),
    div_eq_mul_inv ((Nat.factorial (j + 1) : ℕ) : ℝ) ((2 * π) ^ (j + 2)),
    mul_pow (2 : ℝ) (((Nat.factorial (j + 1) : ℕ) : ℝ) * ((2 * π) ^ (j + 2))⁻¹),
    show (2 : ℝ) ^ ((j + 2) * Module.finrank ℚ F) = ((2 : ℝ) ^ Module.finrank ℚ F) ^ (j + 2) by
      rw [← pow_mul, mul_comm]]
  generalize ((Nat.factorial (j + 1) : ℕ) : ℝ) * ((2 * π) ^ (j + 2))⁻¹ = X
  generalize (∏ i ∈ Finset.range (j + 1), (|(discr F : ℝ)| ^ (1 / 2 : ℝ) *
      ((Nat.factorial (2 * (i + 1) - 1) : ℝ) / (2 * π) ^ (2 * (i + 1))) ^ Module.finrank ℚ F *
        NFEuler.dedekindZetaR F (2 * ((i : ℝ) + 1)))) = P
  have hT2 : (0 : ℝ) < 2 ^ Module.finrank ℚ F := by positivity
  generalize (2 : ℝ) ^ Module.finrank ℚ F = T at hT2 ⊢
  field_simp

end QuadFormsKB.Hanke2005
