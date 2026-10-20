/-
# Local densities over a DVR: $\beta_\pi(m)$ as an explicit finite computation at every prime (Plan A3)

**Layer:** DVR ($R$ a discrete valuation ring with uniformizer $\pi$, finite residue field of size $q$, $2 \ne 0$,
$e = \mathrm{ord}_\pi 2$). The interest is in **dyadic** $\pi \mid N$ of any ramification, where Hanke 2004 says the
densities "must be computed on a case-by-case basis" (p. 362); nothing below assumes $\pi \nmid 2$ or $\pi \nmid N$.

**Proves** that $\beta_\pi(m)$ is an explicit, terminating finite computation:

* **Explicit level** (`DVR.localDensity_eq_level`, `DVR.localDensity_eq_level_J`): for $Q$ nondegenerate, $m \ne 0$ with
  $\pi^{a+1} \nmid m$ and every $K \ge a + K_0$,
  $$\beta_\pi(m) = \frac{r_{\pi^K}(m)}{q^{K(n-1)}}, \qquad K_0 = \mathrm{ord}_\pi(4N) + 1 = \mathrm{ord}_\pi N + 2e + 1,$$
  or $K_0 = L + 2e + 1$ for $Q$ in normal form `IsJordanFormW Q π P w` with all $w_i \le L$. The right side is the number of
  solutions in the finite set $(R/\pi^K)^n$, normalized. The proof runs the Zero-type recursion ($\pi_Z$, p. 359) on top
  of the uniform stabilization of the primitive counts from $K_0$ (Lemma 3.4, `DVR.repCountOf_nonZero_succ`).
* **Units at level $2e+1$, every $Q$** (`DVR.localDensity_unit_eq_level`): for $\pi \nmid m$,
  $\beta_\pi(m) = r_{\pi^{2e+1}}(m)/q^{(2e+1)(n-1)}$, whatever $N$ is (Hanke's "solutions mod $4\mathfrak p$").
* **The recursion, solved** (`DVR.localDensity_eq_dyadicFormula`, `DVR.localDensity_eq_dyadicFormula_J`): with
  $a = \mathrm{ord}_\pi m$, $c_n = q^n/q^{2(n-1)} = q^{2-n}$ (`DVR.zeroFactor`) and the **primitive density at level $K$**
  $\beta^*_K(m) = r^{\mathrm{Good}\cup\mathrm{Bad}}_{\pi^K}(m)/q^{K(n-1)}$ (`DVR.primDensityAt`),
  $$\beta_\pi(m) = \sum_{j=0}^{\lfloor a/2 \rfloor} c_n^{\,j}\; \beta^*_K\!\left(m/\pi^{2j}\right) \qquad (K \ge K_0)$$
  (`DVR.dyadicFormula`). Each $\beta^*_K$ is a count over $(R/\pi^K)^n$ depending only on $m/\pi^{2j} \bmod \pi^K$, and the
  recursion $\beta_\pi(m) = \beta^*_K(m) + c_n\,\beta_\pi(m/\pi^2)$ (`DVR.localDensity_eq_prim_add_zero`) terminates
  after $\lfloor a/2\rfloor$ steps. This is (5.7) of Hanke 2004 without the stability hypothesis.
* **The Bad-map split of the primitive count** (`DVR.repCountOf_nonZero_eq_good_badI_badII`): for $Q$ in normal form and
  $K \ge 3$, $r^{\mathrm{Good}\cup\mathrm{Bad}}_{\pi^K}(m)$ is the Good-type count of $Q$ (determined at level $2e+1$, or $2t+1$ with a
  gradient bound $t$; `DVRDyadic.lean`), plus $q^{s_1+s_2}$ times the Good-type count of $Q'$ at $m/\pi$, level $K - 1$
  ($\pi_{B'}$), plus $q^{2n - s_0 - s_1}$ times the count of $Q''$ at $m/\pi^2$, level $K-2$, with a unit coordinate where
  $w_i \ge 2$ ($\pi_{B''}$), p. 360.

**Depends on** `DVRDepth.lean`.
-/
import QuadFormsKB.LocalDensity.DVRDepth

namespace QuadFormsKB.LocalDensity.DVR

open QuadForm

set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}

section Level

variable [Finite (IsLocalRing.ResidueField R)]

/-- No Zero-type solutions of $Q(\vec x) \equiv m \pmod{\pi^k}$ when $\pi \nmid m$ and $k \ge 1$ (any $Q$). -/
theorem repCountOf_zeroType_eq_zero_of_not_dvd (Q : QuadForm R n) (π : R) {k : ℕ} (hk : 1 ≤ k) {m : R}
    (h1 : ¬ π ∣ m) : repCountOf Q π k m (IsZeroType π k) = 0 := by
  unfold repCountOf
  rw [Nat.card_eq_zero]; left
  refine ⟨fun ⟨x, hx, hz⟩ => h1 ?_⟩
  have := pow_dvd_of_mk_dvd π k 1 hk m (by
    choose y hy using hz
    rw [← hx, show x = fun i => Ideal.Quotient.mk _ π * y i from funext hy, evalIn_const_mul, pow_one]
    exact ⟨Ideal.Quotient.mk _ π * Q.evalIn _ y, by ring⟩)
  rwa [pow_one] at this

/-- For $\pi \nmid m$ and $k \ge 1$ every solution is primitive: $r_{\pi^k}(m) = r^{\mathrm{Good}\cup\mathrm{Bad}}_{\pi^k}(m)$. -/
theorem repCount_eq_nonZero_of_not_dvd (Q : QuadForm R n) (π : R) (hπ : Irreducible π) {k : ℕ} (hk : 1 ≤ k)
    {m : R} (h1 : ¬ π ∣ m) : repCount Q π k m = repCountOf Q π k m (fun x => ¬ IsZeroType π k x) := by
  rw [repCount_eq_zero_add_nonZero Q π hπ, repCountOf_zeroType_eq_zero_of_not_dvd Q π hk h1, zero_add]

/-- $\pi^{2} \cdot (m/\pi^{2})$: the Zero-type count at level $k \ge 2$ in terms of level $k-2$ (map $\pi_Z$, p. 359),
stated with `divPow`. -/
theorem repCountZero_eq_divPow (Q : QuadForm R n) (π : R) (hπ : Irreducible π) {m : R} (h2 : π ^ 2 ∣ m)
    (k : ℕ) (hk : 2 ≤ k) :
    repCountOf Q π k m (IsZeroType π k) = q R ^ n * repCount Q π (k - 2) (divPow π 2 m) :=
  repCountZero_eq Q π hπ m _ (eq_mul_divPow h2) k hk

/-- $\pi^{a+1} \nmid m$ and $\pi^2 \mid m$ give $\pi^{a-1} \nmid m/\pi^2$ and $a \ge 2$. -/
theorem not_dvd_divPow_two {π : R} {a : ℕ} {m : R} (ha : ¬ π ^ (a + 1) ∣ m)
    (h2 : π ^ 2 ∣ m) : 2 ≤ a ∧ ¬ π ^ (a - 2 + 1) ∣ divPow π 2 m := by
  have ha2 : 2 ≤ a := by
    by_contra hlt
    exact ha ((pow_dvd_pow π (by omega)).trans h2)
  refine ⟨ha2, fun hd => ha ?_⟩
  rw [eq_mul_divPow h2, show a + 1 = 2 + (a - 2 + 1) by omega, pow_add]
  exact mul_dvd_mul_left _ hd

/-- **Stabilization of the total count from level $\mathrm{ord}_\pi m + L$**, given stabilization of the primitive
(non-Zero-type) counts from level $L \ge 1$ for every $m$ (Lemma 3.4, p. 361, plus the Zero-type recursion $\pi_Z$):
if $\pi^{a+1} \nmid m$ then $r_{\pi^{k+1}}(m) = q^{n-1} r_{\pi^k}(m)$ for every $k \ge a + L$. -/
theorem repCount_succ_of_nonZero_succ (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (L : ℕ) (hL : 1 ≤ L)
    (hNZ : ∀ (m : R) (k : ℕ), L ≤ k → repCountOf Q π (k + 1) m (fun x => ¬ IsZeroType π (k + 1) x) =
      q R ^ (n - 1) * repCountOf Q π k m (fun x => ¬ IsZeroType π k x)) :
    ∀ (a : ℕ) (m : R), ¬ π ^ (a + 1) ∣ m → ∀ k, a + L ≤ k →
      repCount Q π (k + 1) m = q R ^ (n - 1) * repCount Q π k m := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a IH =>
  intro m ha k hk
  rw [repCount_eq_zero_add_nonZero Q π hπ (k + 1) m, repCount_eq_zero_add_nonZero Q π hπ k m,
    hNZ m k (by omega), mul_add]
  congr 1
  by_cases h2 : π ^ 2 ∣ m
  · obtain ⟨ha2, ha'⟩ := not_dvd_divPow_two ha h2
    rw [repCountZero_eq_divPow Q π hπ h2 (k + 1) (by omega), repCountZero_eq_divPow Q π hπ h2 k (by omega),
      show k + 1 - 2 = (k - 2) + 1 by omega,
      IH (a - 2) (by omega) _ ha' (k - 2) (by omega)]
    ring
  · rw [repCountOf_zeroType_eq_zero Q π (by omega) h2]
    by_cases hk2 : 2 ≤ k
    · rw [repCountOf_zeroType_eq_zero Q π hk2 h2, mul_zero]
    · have ha0 : a = 0 := by omega
      subst ha0
      rw [repCountOf_zeroType_eq_zero_of_not_dvd Q π (by omega) (by simpa using ha), mul_zero]

/-- **Normalized counts are constant from a stabilization level**: if $r_{\pi^{k+1}}(m) = q^{n-1}r_{\pi^k}(m)$ for every
$k \ge K_1$, then $\beta_\pi(m) = r_{\pi^K}(m)/q^{K(n-1)}$ for **every** $K \ge K_1$. -/
theorem localDensity_eq_of_succ (Q : QuadForm R n) (π : R) (m : R) (K₁ : ℕ)
    (hS : ∀ k, K₁ ≤ k → repCount Q π (k + 1) m = q R ^ (n - 1) * repCount Q π k m) (K : ℕ) (hK : K₁ ≤ K) :
    localDensity Q π m = (repCount Q π K m : ℝ) / (q R : ℝ) ^ (K * (n - 1)) := by
  set f : ℕ → ℝ := fun k => (repCount Q π k m : ℝ) / (q R : ℝ) ^ (k * (n - 1)) with hf
  have hq0 : (q R : ℝ) ≠ 0 := by exact_mod_cast (q_pos (R := R)).ne'
  have hstep : ∀ k, K₁ ≤ k → f (k + 1) = f k := by
    intro k hk
    simp only [hf]
    rw [hS k hk]
    push_cast
    rw [show (k + 1) * (n - 1) = (n - 1) + k * (n - 1) by ring, pow_add]
    have : (q R : ℝ) ^ (n - 1) ≠ 0 := pow_ne_zero _ hq0
    field_simp
  have hconst : ∀ k, K₁ ≤ k → f k = f K₁ := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => rfl
    | succ k hk ih => rw [hstep k hk, ih]
  show localDensity Q π m = f K
  rw [hconst K hK]
  exact limUnder_eq_of_eventually (Filter.eventually_atTop.2 ⟨K₁, hconst⟩)

/-- **$\beta_\pi(m)$ at an explicit level, from primitive stabilization at $L$**: if the primitive counts stabilize from
$L \ge 1$ (for every $m$) and $\pi^{a+1} \nmid m$, then $\beta_\pi(m) = r_{\pi^K}(m)/q^{K(n-1)}$ for every $K \ge a + L$. -/
theorem localDensity_eq_level_of_nonZero_succ (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (L : ℕ)
    (hL : 1 ≤ L)
    (hNZ : ∀ (m : R) (k : ℕ), L ≤ k → repCountOf Q π (k + 1) m (fun x => ¬ IsZeroType π (k + 1) x) =
      q R ^ (n - 1) * repCountOf Q π k m (fun x => ¬ IsZeroType π k x))
    {a : ℕ} {m : R} (ha : ¬ π ^ (a + 1) ∣ m) (K : ℕ) (hK : a + L ≤ K) :
    localDensity Q π m = (repCount Q π K m : ℝ) / (q R : ℝ) ^ (K * (n - 1)) :=
  localDensity_eq_of_succ Q π m (a + L)
    (repCount_succ_of_nonZero_succ Q π hπ L hL hNZ a m ha) K hK

/-- **$\beta_\pi(m)$ as a finite count at an explicit level, every prime** (Hanke 2004, (5.2), p. 368, with the depth
bounds of Lemma 3.4, p. 361): for $Q$ nondegenerate over $R$ ($2 \ne 0$, finite residue field, $e = \mathrm{ord}_\pi 2$),
$\pi^{a+1} \nmid m$ and every $K \ge a + \mathrm{ord}_\pi(4N) + 1$ (`depthLevel Q π e` $= \mathrm{ord}_\pi N + 2e + 1$),
$$\beta_\pi(m) = \frac{r_{\pi^K}(m)}{q^{K(n-1)}}.$$
At dyadic $\pi \mid N$ of any ramification this is the explicit formula Hanke 2004 leaves to "a case-by-case basis"
(p. 362): a count over the finite set $(R/\pi^K)^n$. ($m = 0$ is allowed formally, but no $a$ satisfies the hypothesis.) -/
@[kb "hanke2004" "(5.2), p. 368; Lemma 3.4, p. 361 (explicit level at every prime)"]
theorem localDensity_eq_level (Q : QuadForm R n) (hQ : Q.Nondegenerate) (π : R) (hπ : Irreducible π)
    (h20 : (2 : R) ≠ 0) (e : ℕ) (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) {a : ℕ} {m : R}
    (ha : ¬ π ^ (a + 1) ∣ m) (K : ℕ) (hK : a + depthLevel Q π e ≤ K) :
    localDensity Q π m = (repCount Q π K m : ℝ) / (q R : ℝ) ^ (K * (n - 1)) :=
  localDensity_eq_level_of_nonZero_succ Q π hπ (depthLevel Q π e) (by unfold depthLevel; omega)
    (fun m k hk => repCountOf_nonZero_succ Q hQ π hπ h20 e he m k hk) ha K hK

/-- **$\beta_\pi(m)$ at an explicit level for a normal form** (as `localDensity_eq_level`, with the level read off the
blocks): for $Q$ in normal form `IsJordanFormW Q π P w` with all $w_i \le L$, $\pi^{a+1} \nmid m$ and every
$K \ge a + L + 2e + 1$, $\beta_\pi(m) = r_{\pi^K}(m)/q^{K(n-1)}$. -/
@[kb "hanke2004" "(5.2), p. 368; Lemma 3.4, p. 361 (explicit level, normal form)"]
theorem localDensity_eq_level_J (Q : QuadForm R n) (π : R) (hπ : Irreducible π)
    (P : Finset (Fin n × Fin n)) (w : Fin n → ℕ) (hJ : IsJordanFormW Q π P w) (e : ℕ)
    (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) (L : ℕ) (hL : ∀ i, w i ≤ L) {a : ℕ} {m : R}
    (ha : ¬ π ^ (a + 1) ∣ m) (K : ℕ) (hK : a + (L + 2 * e + 1) ≤ K) :
    localDensity Q π m = (repCount Q π K m : ℝ) / (q R : ℝ) ^ (K * (n - 1)) :=
  localDensity_eq_level_of_nonZero_succ Q π hπ (L + 2 * e + 1) (by omega)
    (fun m k hk => repCountOf_nonZero_succ_J Q π hπ P w hJ e he L hL m k hk) ha K hK

/-- **For a unit $m$ every solution of a normal form is of Good type** ($k \ge 1$): Zero-type and Bad-type vectors give
$\pi \mid Q(\vec x)$. -/
theorem repCount_eq_good_of_not_dvd (Q : QuadForm R n) (π : R) (hπ : Irreducible π)
    (P : Finset (Fin n × Fin n)) (w : Fin n → ℕ) (hJ : IsJordanFormW Q π P w) {k : ℕ} (hk : 1 ≤ k) {m : R}
    (hm : ¬ π ∣ m) : repCount Q π k m = repCountOf Q π k m (IsGoodType (unimodularCoords w) π k) := by
  rw [repCount_eq_add_types Q π hπ (unimodularCoords w) k m,
    repCountOf_zeroType_eq_zero_of_not_dvd Q π hk hm,
    repCountOf_eq_zero_of_not_dvd Q π P w hJ m k 1 (by omega) hk (by rwa [pow_one])
      (IsBadType (unimodularCoords w) π k) (fun x hx i hi => by
      by_contra h
      exact hx.2 ⟨hx.1, i, by simp [unimodularCoords]; omega, h⟩)]
  simp

/-- **Unit densities at level $2e + 1$ for every nondegenerate $Q$, every prime** (Hanke 2004, Remark 3.4.1(a), p. 361,
and the "solutions mod $4\mathfrak p$" of p. 359 and p. 362, now for **every** $\mathfrak p \mid 2$, including $\mathfrak p \mid N$
of any ramification): for $\pi \nmid m$,
$$\beta_\pi(m) = \frac{r_{\pi^{2e+1}}(m)}{q^{(2e+1)(n-1)}}, \qquad e = \mathrm{ord}_\pi 2.$$
*Proof:* in a normal form (`exists_jordanFormW`, same counts) all solutions of a unit are of Good type
(`repCount_eq_good_of_not_dvd`), and Good-type counts lift from level $2e + 1$ (`repCountGood_add`).
*Update (candidate; pending author; `docs/updates-and-errata.md`):* p. 362 leaves the dyadic case to "a case-by-case
basis"; for units the solutions mod $4\mathfrak p$ always suffice, whatever $N$ is. -/
@[kb "hanke2004" "Remark 3.4.1(a), p. 361; p. 359, p. 362 (\"mod 4𝔭\", every dyadic 𝔭)"]
theorem localDensity_unit_eq_level (Q : QuadForm R n) (hQ : Q.Nondegenerate) (π : R) (hπ : Irreducible π)
    (h20 : (2 : R) ≠ 0) (e : ℕ) (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) {m : R} (hm : ¬ π ∣ m) (K : ℕ)
    (hK : 2 * e + 1 ≤ K) :
    localDensity Q π m = (repCount Q π K m : ℝ) / (q R : ℝ) ^ (K * (n - 1)) := by
  obtain ⟨Q', P, w, hJ, -, hc⟩ := exists_jordanFormW Q hQ π hπ h20
  have hloc : localDensity Q π m = localDensity Q' π m := by
    unfold localDensity; simp only [hc]
  rw [hloc, hc]
  refine localDensity_eq_of_succ Q' π m (2 * e + 1) (fun k hk => ?_) K hK
  rw [repCount_eq_good_of_not_dvd Q' π hπ P w hJ (by omega) hm,
    repCount_eq_good_of_not_dvd Q' π hπ P w hJ (by omega) hm,
    repCountGood_add Q' π hπ P w hJ e he m k 1 hk, mul_one]

end Level

/-! ### The Zero-type recursion, solved -/

section Formula

variable [Finite (IsLocalRing.ResidueField R)]

/-- **The primitive density at level $K$**: $\beta^*_K(m) = r^{\mathrm{Good}\cup\mathrm{Bad}}_{\pi^K}(m)/q^{K(n-1)}$, the normalized
number of solutions of $Q(\vec x) \equiv m \pmod{\pi^K}$ with some $x_i$ a unit (Hanke 2004, Def. 3.1 and Def. 5.1). -/
noncomputable def primDensityAt (Q : QuadForm R n) (π : R) (K : ℕ) (m : R) : ℝ :=
  (repCountOf Q π K m (fun x => ¬ IsZeroType π K x) : ℝ) / (q R : ℝ) ^ (K * (n - 1))

/-- **The factor of the map $\pi_Z$**: $c_n = q^n / q^{2(n-1)}$ ($= q^{2-n}$; written so that it is right for $n = 1$ too). -/
noncomputable def zeroFactor (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (n : ℕ) : ℝ :=
  (q R : ℝ) ^ n / (q R : ℝ) ^ (2 * (n - 1))

/-- **The dyadic formula** for $\beta_\pi(m)$, $a = \mathrm{ord}_\pi m$:
$\sum_{j=0}^{\lfloor a/2\rfloor} c_n^{\,j}\,\beta^*_K(m/\pi^{2j})$ (`localDensity_eq_dyadicFormula`). A finite sum of finite counts. -/
noncomputable def dyadicFormula (Q : QuadForm R n) (π : R) (K a : ℕ) (m : R) : ℝ :=
  ∑ j ∈ Finset.range (a / 2 + 1), zeroFactor R n ^ j * primDensityAt Q π K (divPow π (2 * j) m)

/-- Primitive normalized counts are constant from a primitive stabilization level. -/
theorem primDensityAt_eq_of_ge (Q : QuadForm R n) (π : R) (L : ℕ)
    (hNZ : ∀ (m : R) (k : ℕ), L ≤ k → repCountOf Q π (k + 1) m (fun x => ¬ IsZeroType π (k + 1) x) =
      q R ^ (n - 1) * repCountOf Q π k m (fun x => ¬ IsZeroType π k x))
    (m : R) (K k : ℕ) (hK : L ≤ K) (hk : K ≤ k) : primDensityAt Q π k m = primDensityAt Q π K m := by
  have hq0 : (q R : ℝ) ≠ 0 := by exact_mod_cast (q_pos (R := R)).ne'
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rw [← ih]
    unfold primDensityAt
    rw [hNZ m k (by omega)]
    push_cast
    rw [show (k + 1) * (n - 1) = (n - 1) + k * (n - 1) by ring, pow_add]
    have : (q R : ℝ) ^ (n - 1) ≠ 0 := pow_ne_zero _ hq0
    field_simp

open Classical in
/-- **One step of the recursion**: under primitive stabilization from $L \ge 1$, for $\pi^{a+1} \nmid m$ and $K \ge L$,
$$\beta_\pi(m) = \beta^*_K(m) + [\pi^2 \mid m]\; c_n\, \beta_\pi(m/\pi^2).$$ -/
theorem localDensity_eq_prim_add_zero_of (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (L : ℕ) (hL : 1 ≤ L)
    (hNZ : ∀ (m : R) (k : ℕ), L ≤ k → repCountOf Q π (k + 1) m (fun x => ¬ IsZeroType π (k + 1) x) =
      q R ^ (n - 1) * repCountOf Q π k m (fun x => ¬ IsZeroType π k x))
    {a : ℕ} {m : R} (ha : ¬ π ^ (a + 1) ∣ m) (K : ℕ) (hK : L ≤ K) :
    localDensity Q π m = primDensityAt Q π K m +
      if π ^ 2 ∣ m then zeroFactor R n * localDensity Q π (divPow π 2 m) else 0 := by
  have hq0 : (q R : ℝ) ≠ 0 := by exact_mod_cast (q_pos (R := R)).ne'
  set k := a + L + K + 2 with hkdef
  rw [localDensity_eq_level_of_nonZero_succ Q π hπ L hL hNZ ha k (by omega),
    ← primDensityAt_eq_of_ge Q π L hNZ m K k hK (by omega), repCount_eq_zero_add_nonZero Q π hπ k m,
    Nat.cast_add, add_div, add_comm]
  unfold primDensityAt
  congr 1
  split_ifs with h2
  · obtain ⟨ha2, ha'⟩ := not_dvd_divPow_two ha h2
    rw [repCountZero_eq_divPow Q π hπ h2 k (by omega),
      localDensity_eq_level_of_nonZero_succ Q π hπ L hL hNZ ha' (k - 2) (by omega), zeroFactor,
      show k * (n - 1) = 2 * (n - 1) + (k - 2) * (n - 1) by
        rw [← add_mul]; congr 1; omega, pow_add]
    push_cast
    field_simp
  · rw [repCountOf_zeroType_eq_zero Q π (by omega) h2]
    simp

/-- `divPow` composes: $(m/\pi^2)/\pi^{2j} = m/\pi^{2(j+1)}$ when $\pi^{2(j+1)} \mid m$. -/
theorem divPow_divPow_two {π : R} (hπ : π ≠ 0) (j : ℕ) {m : R} (h : π ^ (2 * (j + 1)) ∣ m) :
    divPow π (2 * j) (divPow π 2 m) = divPow π (2 * (j + 1)) m := by
  have h2 : π ^ 2 ∣ m := (pow_dvd_pow π (by omega)).trans h
  have hj : π ^ (2 * j) ∣ divPow π 2 m := by
    have h' := h
    rw [eq_mul_divPow h2, show 2 * (j + 1) = 2 + 2 * j by ring, pow_add] at h'
    exact (mul_dvd_mul_iff_left (pow_ne_zero 2 hπ)).1 h'
  have e1 := eq_mul_divPow h
  have e2 := eq_mul_divPow h2
  have e3 := eq_mul_divPow hj
  apply mul_left_cancel₀ (pow_ne_zero (2 * (j + 1)) hπ)
  have key : π ^ (2 * (j + 1)) * divPow π (2 * j) (divPow π 2 m) = m := by
    rw [show 2 * (j + 1) = 2 + 2 * j by ring, pow_add, mul_assoc, ← e3, ← e2]
  rw [key]; exact e1

/-- **The recursion solved, from primitive stabilization at $L$**: if $\pi^a \,\|\, m$ and $K \ge L \ge 1$, then
$\beta_\pi(m) = \sum_{j=0}^{\lfloor a/2\rfloor} c_n^{\,j}\, \beta^*_K(m/\pi^{2j})$. -/
theorem localDensity_eq_dyadicFormula_of (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (L : ℕ) (hL : 1 ≤ L)
    (hNZ : ∀ (m : R) (k : ℕ), L ≤ k → repCountOf Q π (k + 1) m (fun x => ¬ IsZeroType π (k + 1) x) =
      q R ^ (n - 1) * repCountOf Q π k m (fun x => ¬ IsZeroType π k x))
    (K : ℕ) (hK : L ≤ K) :
    ∀ (a : ℕ) (m : R), π ^ a ∣ m → ¬ π ^ (a + 1) ∣ m →
      localDensity Q π m = dyadicFormula Q π K a m := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a IH =>
  intro m hda ha
  rw [localDensity_eq_prim_add_zero_of Q π hπ L hL hNZ ha K hK]
  unfold dyadicFormula
  split_ifs with h2
  · obtain ⟨ha2, ha'⟩ := not_dvd_divPow_two ha h2
    have hda' : π ^ (a - 2) ∣ divPow π 2 m := by
      have h' := hda
      rw [eq_mul_divPow h2, show a = 2 + (a - 2) by omega, pow_add] at h'
      exact (mul_dvd_mul_iff_left (pow_ne_zero 2 hπ.ne_zero)).1 h'
    rw [IH (a - 2) (by omega) _ hda' ha', dyadicFormula, show a / 2 + 1 = (a - 2) / 2 + 1 + 1 by omega,
      Finset.sum_range_succ' (fun j => zeroFactor R n ^ j * primDensityAt Q π K (divPow π (2 * j) m))]
    simp only [pow_zero, one_mul, mul_zero, divPow_zero, Finset.mul_sum]
    rw [add_comm (primDensityAt Q π K m)]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [divPow_divPow_two hπ.ne_zero j ((pow_dvd_pow π (by omega)).trans hda), pow_succ]
    ring
  · have ha2 : a / 2 = 0 := by
      by_contra h
      exact h2 ((pow_dvd_pow π (by omega)).trans hda)
    rw [ha2, zero_add, Finset.sum_range_one, pow_zero, one_mul, mul_zero, divPow_zero, add_zero]

/-- **$\beta_\pi(m)$ by the dyadic formula, every nondegenerate $Q$, every prime** (Hanke 2004, §3 and (5.7), p. 369,
without the stability hypothesis; the explicit form that p. 362 leaves to "a case-by-case basis" at $\mathfrak p \mid 2$):
for $\pi^a \,\|\, m$ and every $K \ge \mathrm{ord}_\pi(4N) + 1$ (`depthLevel Q π e`),
$$\beta_\pi(m) = \sum_{j=0}^{\lfloor a/2\rfloor} q^{j(2-n)}\, \frac{r^{\mathrm{Good}\cup\mathrm{Bad}}_{\pi^K}(m/\pi^{2j})}{q^{K(n-1)}}.$$
Each term is a count over $(R/\pi^K)^n$; the sum has $\lfloor a/2 \rfloor + 1$ terms.
*Update (candidate; pending author; `docs/updates-and-errata.md`):* this is (5.7) without the $\mathfrak p$-stability hypothesis,
and the explicit dyadic formula that p. 362 leaves to "a case-by-case basis". -/
@[kb "hanke2004" "§3, (5.7), p. 369; p. 362 (dyadic case-by-case), explicit"]
theorem localDensity_eq_dyadicFormula (Q : QuadForm R n) (hQ : Q.Nondegenerate) (π : R) (hπ : Irreducible π)
    (h20 : (2 : R) ≠ 0) (e : ℕ) (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) (K : ℕ) (hK : depthLevel Q π e ≤ K)
    {a : ℕ} {m : R} (hda : π ^ a ∣ m) (ha : ¬ π ^ (a + 1) ∣ m) :
    localDensity Q π m = dyadicFormula Q π K a m :=
  localDensity_eq_dyadicFormula_of Q π hπ (depthLevel Q π e) (by unfold depthLevel; omega)
    (fun m k hk => repCountOf_nonZero_succ Q hQ π hπ h20 e he m k hk) K hK a m hda ha

/-- **$\beta_\pi(m)$ by the dyadic formula for a normal form** `IsJordanFormW Q π P w` with all $w_i \le L$: for
$\pi^a \,\|\, m$ and every $K \ge L + 2e + 1$, $\beta_\pi(m) = \sum_{j=0}^{\lfloor a/2\rfloor} c_n^{\,j}\,\beta^*_K(m/\pi^{2j})$ —
an explicit computation in $e$, $f$ (through $q = 2^f$), the block data mod $\pi^K$, and $m$. -/
@[kb "hanke2004" "§3, (5.7), p. 369 (explicit, normal form)"]
theorem localDensity_eq_dyadicFormula_J (Q : QuadForm R n) (π : R) (hπ : Irreducible π)
    (P : Finset (Fin n × Fin n)) (w : Fin n → ℕ) (hJ : IsJordanFormW Q π P w) (e : ℕ)
    (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) (L : ℕ) (hL : ∀ i, w i ≤ L) (K : ℕ) (hK : L + 2 * e + 1 ≤ K)
    {a : ℕ} {m : R} (hda : π ^ a ∣ m) (ha : ¬ π ^ (a + 1) ∣ m) :
    localDensity Q π m = dyadicFormula Q π K a m :=
  localDensity_eq_dyadicFormula_of Q π hπ (L + 2 * e + 1) (by omega)
    (fun m k hk => repCountOf_nonZero_succ_J Q π hπ P w hJ e he L hL m k hk) K hK a m hda ha

open Classical in
/-- **The recursion step, every nondegenerate $Q$**: $\beta_\pi(m) = \beta^*_K(m) + [\pi^2 \mid m]\,c_n\,\beta_\pi(m/\pi^2)$
for $m \ne 0$ and $K \ge \mathrm{ord}_\pi(4N) + 1$. -/
theorem localDensity_eq_prim_add_zero (Q : QuadForm R n) (hQ : Q.Nondegenerate) (π : R) (hπ : Irreducible π)
    (h20 : (2 : R) ≠ 0) (e : ℕ) (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) {m : R} (hm : m ≠ 0) (K : ℕ)
    (hK : depthLevel Q π e ≤ K) :
    localDensity Q π m = primDensityAt Q π K m +
      if π ^ 2 ∣ m then zeroFactor R n * localDensity Q π (divPow π 2 m) else 0 := by
  obtain ⟨a, -, ha⟩ := exists_pow_dvd_not_dvd π hπ hm
  exact localDensity_eq_prim_add_zero_of Q π hπ (depthLevel Q π e) (by unfold depthLevel; omega)
    (fun m k hk => repCountOf_nonZero_succ Q hQ π hπ h20 e he m k hk) ha K hK

open Classical in
/-- **The recursion step for a normal form** with all $w_i \le L$: for $m \ne 0$ and $K \ge L + 2e + 1$,
$\beta_\pi(m) = \beta^*_K(m) + [\pi^2 \mid m]\,c_n\,\beta_\pi(m/\pi^2)$. -/
theorem localDensity_eq_prim_add_zero_J (Q : QuadForm R n) (π : R) (hπ : Irreducible π)
    (P : Finset (Fin n × Fin n)) (w : Fin n → ℕ) (hJ : IsJordanFormW Q π P w) (e : ℕ)
    (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) (L : ℕ) (hL : ∀ i, w i ≤ L) {m : R} (hm : m ≠ 0) (K : ℕ)
    (hK : L + 2 * e + 1 ≤ K) :
    localDensity Q π m = primDensityAt Q π K m +
      if π ^ 2 ∣ m then zeroFactor R n * localDensity Q π (divPow π 2 m) else 0 := by
  obtain ⟨a, -, ha⟩ := exists_pow_dvd_not_dvd π hπ hm
  exact localDensity_eq_prim_add_zero_of Q π hπ (L + 2 * e + 1) (by omega)
    (fun m k hk => repCountOf_nonZero_succ_J Q π hπ P w hJ e he L hL m k hk) ha K hK

/-- `divPow` is exact division: if $r = \pi^e s$ then $r/\pi^e = s$. -/
theorem divPow_eq_of_eq_mul {π : R} (hπ : π ≠ 0) {e : ℕ} {r s : R} (h : r = π ^ e * s) :
    divPow π e r = s := by
  rw [h, ← mul_one (π ^ e), mul_assoc, one_mul, divPow_pow_mul hπ le_rfl, Nat.sub_self, pow_zero, one_mul]

end Formula

/-! ### The Bad-map split of the primitive count (maps $\pi_{B'}$, $\pi_{B''}$, p. 360) -/

section BadSplit

variable [Finite (IsLocalRing.ResidueField R)]

open Classical in
/-- **The primitive count of a normal form through the maps of §3** (Hanke 2004, Def. 3.1, maps $\pi_{B'}$ and
$\pi_{B''}$, p. 360): for $Q$ in normal form `IsJordanFormW Q π P w`, $k \ge 3$, $Q' = $ `badIForm Q π w`,
$Q'' = $ `badIIForm Q π w`, $S_0 = \{w_i = 0\}$, $s_{\ge1} = \#\{w_i \ge 1\}$, $s_{\le 1} = \#\{w_i \le 1\}$:
$$r^{\mathrm{Good}\cup\mathrm{Bad}}_{\pi^k}(m) = r^{\mathrm{Good}}_{\pi^k}(m)
  + [\pi \mid m]\, q^{s_{\ge1}}\, r^{\mathrm{Good}(Q')}_{\pi^{k-1}}(m/\pi)
  + [\pi^2 \mid m]\, q^{2n - s_{\le1}}\, r^{(Q'';\ \exists i,\ w_i \ge 2,\ \pi \nmid x_i)}_{\pi^{k-2}}(m/\pi^2).$$
Good type of $Q'$ is relative to `unimodularCoords (nuI w)`. The Good-type terms are determined at level $2e+1$
(`DVR.repCountGood_add`, or $2t+1$ under a gradient bound, `DVR.repCountGood_add_of_gradBound`); the last term is a
pattern count of $Q''$, whose exponents are $w_i - 2$ (`DVR.isJordanFormW_badI_badII`), so iterating lowers all
$w_i$ (the recursion behind `DVR.repCountOf_unitOn_succ`). -/
@[kb "hanke2004" "§3, maps π_{B'}, π_{B''}, p. 360 (primitive count split)"]
theorem repCountOf_nonZero_eq_good_badI_badII (Q : QuadForm R n) (π : R) (hπ : Irreducible π)
    (P : Finset (Fin n × Fin n)) (w : Fin n → ℕ) (hJ : IsJordanFormW Q π P w) (m : R) (k : ℕ)
    (hk : 3 ≤ k) :
    repCountOf Q π k m (fun x => ¬ IsZeroType π k x) =
      repCountOf Q π k m (IsGoodType (unimodularCoords w) π k) +
      (if π ∣ m then q R ^ ((Finset.univ.filter fun i => 1 ≤ w i).card) *
          repCountOf (badIForm Q π w) π (k - 1) (divPow π 1 m)
            (IsGoodType (unimodularCoords (nuI w)) π (k - 1)) else 0) +
      (if π ^ 2 ∣ m then q R ^ (2 * n - (Finset.univ.filter fun i => w i ≤ 1).card) *
          repCountOf (badIIForm Q π w) π (k - 2) (divPow π 2 m)
            (fun y => ∃ i, 2 ≤ w i ∧ ¬ Ideal.Quotient.mk _ π ∣ y i) else 0) := by
  have := finite_quot_pow π hπ k
  rw [repCountOf_nonZero_eq_good_add_bad Q π hπ (unimodularCoords w) k m, add_assoc]
  congr 1
  have hsplit : repCountOf Q π k m (IsBadType (unimodularCoords w) π k) =
      repCountOf Q π k m (fun x => IsBadType (unimodularCoords w) π k x ∧
        ∃ i, w i = 1 ∧ ¬ Ideal.Quotient.mk _ π ∣ x i) +
      repCountOf Q π k m (fun x => IsBadType (unimodularCoords w) π k x ∧
        ∀ i, w i = 1 → Ideal.Quotient.mk _ π ∣ x i) := by
    unfold repCountOf
    refine natCard_split _ _ _ (fun x => ∃ i, w i = 1 ∧ ¬ Ideal.Quotient.mk _ π ∣ x i)
      (fun x => ?_) (fun x => ?_)
    · tauto
    · simp only [not_exists, not_and, not_not]; tauto
  have hbad0 : ∀ x : Fin n → R ⧸ Ideal.span {π ^ k}, IsBadType (unimodularCoords w) π k x →
      ∀ i, w i < 1 → Ideal.Quotient.mk _ π ∣ x i := by
    intro x hx i hi
    by_contra h
    exact hx.2 ⟨hx.1, i, by simp [unimodularCoords]; omega, h⟩
  rw [hsplit]
  congr 1
  · split_ifs with h1
    · exact repCountBadI_eq Q _ π hπ P w hJ (fun i j => badIForm_rel hJ i j) m _
        (by
          have := eq_mul_divPow (π := π) (e := 1) (r := m) (by rwa [pow_one])
          rwa [pow_one] at this) k (by omega)
    · exact repCountOf_eq_zero_of_not_dvd Q π P w hJ m k 1 (by omega) (by omega) (by rwa [pow_one])
        _ (fun x hx => hbad0 x hx.1)
  · split_ifs with h2
    · exact repCountBadII_eq Q _ π hπ P w hJ (fun i j => badIIForm_rel hJ i j) m _
        (eq_mul_divPow h2) k hk
    · refine repCountOf_eq_zero_of_not_dvd Q π P w hJ m k 2 le_rfl (by omega) h2 _ fun x hx i hi => ?_
      rcases (show w i = 0 ∨ w i = 1 by omega) with h | h
      · exact hbad0 x hx.1 i (by omega)
      · exact hx.2 i h

end BadSplit

end QuadFormsKB.LocalDensity.DVR
