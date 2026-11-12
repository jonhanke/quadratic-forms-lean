/-
# The Eichler class number formula and the trace formula over $\mathbb Q$: statements (Voight, Ch. 30, 41)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021, Main Theorem 30.8.6,
Theorem 41.1.13, Main Theorem 41.5.2 and Example 41.5.8 (key `voight2021`).

**Setting.** $B = (a, b \mid \mathbb Q)$ = `QuatF ℚ a b` is a definite quaternion algebra over $\mathbb Q$
(`IsTotDefinite a b`), of discriminant $D = \prod_{p \in \operatorname{Ram}_f(B)} p$, and $\mathcal O \subset B$ is a
maximal order (`IsMaximalOrder`). As in `Voight/MassFormula.lean`, ideal classes are classes of nonzero left
ideals of $\mathcal O$ under $J \sim J\beta$ (`QuatOrder.idealSetoid`); Voight uses right ideals, and the
standard involution exchanges the two conventions.

**Statements** (named propositions, not proved here):
* `EichlerClassNumberFormulaMassRat` (Main Theorem 30.8.6 for $F = \mathbb Q$, maximal orders):
  $\# \operatorname{Cls}\mathcal O = \operatorname{mass}(\operatorname{Cls}\mathcal O) + \tfrac14 m(\mathbb Z[i], \mathcal O; \mathcal O^\times)
  + \tfrac13 m(\mathbb Z[\omega], \mathcal O; \mathcal O^\times)$, where $m(S, \mathcal O; \mathcal O^\times)$ is the number of
  $\mathcal O^\times$-conjugacy classes of (optimal) embeddings $S \hookrightarrow \mathcal O$.
* `BrandtTraceFormulaRat` (Theorem 41.1.13, **corrected**; see below): the trace of the $n$-th Brandt matrix is
  $$\operatorname{tr} T(n) = \sum_{t \in \mathbb Z,\ t^2 < 4n} H_D(t^2 - 4n) + \begin{cases} \varphi(D)/12, & n \text{ a square},\\
  0, & \text{otherwise},\end{cases}$$
  with the modified Hurwitz class number $H_D(\Delta) = \sum_{S} \frac{h(S)}{w(S)} \prod_{p \mid D} m_p(S)$ summed
  over the imaginary quadratic orders $S$ of discriminant $\Delta / g^2$, $g \ge 1$ (Example 41.5.8, (41.5.10)).

*Erratum (Theorem 41.1.13).* The printed theorem defines $h_D(d') = h_D(d)$ for a non-fundamental
discriminant $d' = d f^2$ (only the maximal order is counted). This is wrong: for the Hurwitz order
($D = 2$, $\# \operatorname{Cls}\mathcal O = 1$, so $T(9) = [\sigma(9)] = [13]$ by Example 41.5.12) the printed formula gives
$\operatorname{tr} T(9) = 10$, while summing over all orders $S \supseteq \mathbb Z[(t + \sqrt{t^2 - 4n})/2]$, as in
Example 41.5.8, gives $13$. The statement here uses the corrected (summed) $H_D$.

**Proved here** (`eichlerClassNumberFormulaRat_of_brandtTraceFormulaRat`): the trace formula at $n = 1$
gives the Eichler class number formula of Theorem 30.1.5 (`EichlerClassNumberFormulaRat`), since $T(1)$ is the
identity matrix and $h(-4) = h(-3) = 1$; this checks that the two statements are consistent.
-/
import QuadFormsKB.Literature.Voight.MassFormula
import QuadFormsKB.Siegel.ThetaCharacter

open NumberField Quaternion

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Voight

open QuadFormsKB.Quat QuadFormsKB.QuatOrder QuadFormsKB.NFEuler

/-! ## Optimal embeddings and the class number formula -/

/-- **Optimal embeddings of $\mathbb Z[i]$ up to conjugation**, $m(\mathbb Z[i], \mathcal O; \mathcal O^\times)$
(Voight 2021, 30.3 and 30.8.3): an embedding $\varphi : \mathbb Z[i] \hookrightarrow \mathcal O$ is determined by
$x = \varphi(i)$, an element with $x^2 = -1$; it is automatically optimal since $\mathbb Z[i]$ is a maximal order;
two embeddings are $\mathcal O^\times$-conjugate iff their values at $i$ are. So this is the number of
$\mathcal O^\times$-conjugacy classes (`ConjClasses`) of $x \in \mathcal O$ with $x^2 = -1$. -/
@[kb "voight2021" "30.8.3, (30.8.4), p. 561"]
def embNumGaussian {F : Type} [Field F] [NumberField F] {a b : 𝓞 F}
    (O : Subalgebra (𝓞 F) (QuatF F a b)) : ℕ :=
  Nat.card {c : ConjClasses O // ∃ x : O, ConjClasses.mk x = c ∧ x * x = -1}

/-- **Optimal embeddings of $\mathbb Z[\omega]$ up to conjugation**, $\omega^2 + \omega + 1 = 0$: the number of
$\mathcal O^\times$-conjugacy classes of $x \in \mathcal O$ with $x^2 + x + 1 = 0$ (as for `embNumGaussian`;
$\mathbb Z[\omega]$ is a maximal order, so every embedding is optimal). -/
@[kb "voight2021" "30.8.3, (30.8.4), p. 561"]
def embNumEisenstein {F : Type} [Field F] [NumberField F] {a b : 𝓞 F}
    (O : Subalgebra (𝓞 F) (QuatF F a b)) : ℕ :=
  Nat.card {c : ConjClasses O // ∃ x : O, ConjClasses.mk x = c ∧ x * x + x + 1 = 0}

/-- **The Eichler class number formula, mass form, over $\mathbb Q$** (Voight 2021, Main Theorem 30.8.6 with
$R = \mathbb Z$, $T = \{\infty\}$, for maximal orders), as a named proposition: for a definite quaternion algebra
$B = (a,b \mid \mathbb Q)$ and a maximal order $\mathcal O \subset B$,
$$\# \operatorname{Cls}\mathcal O = \operatorname{mass}(\operatorname{Cls}\mathcal O)
+ \frac14\, m(\mathbb Z[i], \mathcal O; \mathcal O^\times) + \frac13\, m(\mathbb Z[\omega], \mathcal O; \mathcal O^\times).$$
In 30.8.6 the sum runs over quadratic $\mathbb Z$-orders $S$ with $q = [S^\times : \mathbb Z^\times] \ge 2$, weighted by
$\tfrac12(1 - \tfrac1q) h(S)$; in a definite algebra only imaginary quadratic orders embed, and those with
$q \ge 2$ are $\mathbb Z[i]$ ($q = 2$, weight $\tfrac14$) and $\mathbb Z[\omega]$ ($q = 3$, weight $\tfrac13$), both of
class number $1$. Stated, not proved here. -/
@[kb "voight2021" "Main Theorem 30.8.6, p. 562"]
def EichlerClassNumberFormulaMassRat : Prop :=
  ∀ (a b : 𝓞 ℚ), a ≠ 0 → b ≠ 0 → IsTotDefinite a b →
    ∀ O : Subalgebra (𝓞 ℚ) (QuatF ℚ a b), IsMaximalOrder (𝓞 ℚ) ℚ O →
      (Nat.card {c : Quotient (idealSetoid O) // c.out ≠ ⊥} : ℝ) =
        classMass O + (embNumGaussian O : ℝ) / 4 + (embNumEisenstein O : ℝ) / 3

/-! ## Brandt matrices and the trace formula -/

/-- **The trace of the $n$-th Brandt matrix** (Voight 2021, (41.1.1)):
$\operatorname{tr} T(n) = \sum_{[I]} \#\{J \subseteq I : [I : J] = n^2,\ [J] = [I]\}$, the sum over the classes of
nonzero (integral, left) ideals $I$ of $\mathcal O$ (one representative `c.out` per class), counting the
subideals $J \subseteq I$ of index $n^2$ in the same class as $I$. (For a maximal order every nonzero ideal is
invertible, and $[I : J] = n^2$ iff $\operatorname{nrd}(J) = n \operatorname{nrd}(I)$.) -/
@[kb "voight2021" "(41.1.1), p. 763"]
def brandtTrace {a b : 𝓞 ℚ} (O : Subalgebra (𝓞 ℚ) (QuatF ℚ a b)) (n : ℕ) : ℝ :=
  ∑' c : {c : Quotient (idealSetoid O) // c.out ≠ ⊥},
    (Set.ncard {J : Ideal O | J ≤ c.1.out ∧
      J.toAddSubgroup.relIndex c.1.out.toAddSubgroup = n ^ 2 ∧ (idealSetoid O) J c.1.out} : ℝ)

/-- $\Delta \in \mathbb Z$ is a discriminant: $\Delta \equiv 0, 1 \pmod 4$. -/
def IsDiscr (Δ : ℤ) : Prop := Δ % 4 = 0 ∨ Δ % 4 = 1

instance (Δ : ℤ) : Decidable (IsDiscr Δ) := by unfold IsDiscr; infer_instance

/-- **The class number $h(\Delta)$ of the imaginary quadratic order of discriminant $\Delta < 0$**, as the
number of reduced primitive positive definite binary forms $Ax^2 + Bxy + Cy^2$ of discriminant
$B^2 - 4AC = \Delta$: $\gcd(A, B, C) = 1$, $|B| \le A \le C$, and $B \ge 0$ if $|B| = A$ or $A = C$ (each proper
equivalence class has exactly one reduced form; Gauss, see Voight 30.4 / Cox Thm. 2.8). -/
def formClassNumber (Δ : ℤ) : ℕ :=
  Set.ncard {f : ℤ × ℤ × ℤ | f.2.1 ^ 2 - 4 * f.1 * f.2.2 = Δ ∧
    Int.gcd (Int.gcd f.1 f.2.1 : ℤ) f.2.2 = 1 ∧ |f.2.1| ≤ f.1 ∧ f.1 ≤ f.2.2 ∧
    ((|f.2.1| = f.1 ∨ f.1 = f.2.2) → 0 ≤ f.2.1)}

/-- **The number of units** $\# S^\times$ of the imaginary quadratic order $S$ of discriminant $\Delta < 0$:
$6$ for $\Delta = -3$, $4$ for $\Delta = -4$, $2$ otherwise. -/
def unitCount (Δ : ℤ) : ℕ := if Δ = -3 then 6 else if Δ = -4 then 4 else 2

/-- **The local embedding number at a prime $p \mid D$** of the order $S$ of discriminant $\Delta$ into the
maximal order of the division algebra over $\mathbb Q_p$ (Voight 30.5.3): $0$ if $p$ divides the conductor
of $S$ (i.e. $p^2 \mid \Delta$ and $\Delta/p^2$ is a discriminant), and $1 - \left(\frac{\Delta}{p}\right)$ otherwise
(Kronecker symbol, `Siegel.kroneckerSym`; for $p \nmid$ conductor it equals $1 - (d_K/p)$). -/
def localEmb (Δ : ℤ) (p : ℕ) : ℤ :=
  if ((p : ℤ) ^ 2 ∣ Δ ∧ IsDiscr (Δ / (p : ℤ) ^ 2)) then 0 else 1 - Siegel.kroneckerSym Δ p

/-- **The modified Hurwitz class number** $H_D(\Delta)$ (Voight Example 41.5.8, (41.5.10), with Theorem 41.1.13's
normalization by the full unit group): for $\Delta < 0$ and the primes $p_v$, $v \in P$, dividing $D$,
$$H_D(\Delta) = \sum_{\substack{g \ge 1,\ g^2 \mid \Delta \\ \Delta/g^2 \equiv 0, 1 \ (4)}}
\frac{h(\Delta/g^2)}{\# S_{\Delta/g^2}^\times} \prod_{v \in P} m_{p_v}(\Delta/g^2),$$
the sum over the imaginary quadratic orders containing the order of discriminant $\Delta$. -/
def modHurwitz {ι : Type*} (P : Finset ι) (prime : ι → ℕ) (Δ : ℤ) : ℝ :=
  ∑ g ∈ Finset.Icc 1 Δ.natAbs,
    if ((g : ℤ) ^ 2 ∣ Δ ∧ IsDiscr (Δ / (g : ℤ) ^ 2)) then
      (formClassNumber (Δ / (g : ℤ) ^ 2) : ℝ) / unitCount (Δ / (g : ℤ) ^ 2) *
        ∏ v ∈ P, (localEmb (Δ / (g : ℤ) ^ 2) (prime v) : ℝ)
    else 0

/-- **The trace formula for Brandt matrices over $\mathbb Q$** (Voight 2021, Theorem 41.1.13, corrected as in
the module docstring; a special case of Main Theorem 41.5.2 by Example 41.5.8), as a named proposition: for a
definite quaternion algebra $B = (a, b \mid \mathbb Q)$ of discriminant $D$, a maximal order $\mathcal O \subset B$ and
$n \ge 1$,
$$\operatorname{tr} T(n) = \sum_{t \in \mathbb Z,\ t^2 < 4n} H_D(t^2 - 4n) +
\begin{cases} \varphi(D)/12, & n \text{ a square}, \\ 0, & \text{otherwise}, \end{cases}$$
with $\varphi(D) = \prod_{p \mid D}(p - 1)$ and $H_D$ = `modHurwitz` (sum over all orders). Stated, not proved. -/
@[kb "voight2021" "Theorem 41.1.13, p. 767 (corrected); Main Theorem 41.5.2, p. 775"]
def BrandtTraceFormulaRat : Prop :=
  ∀ (a b : 𝓞 ℚ) (ha : a ≠ 0) (hb : b ≠ 0), IsTotDefinite a b →
    ∀ O : Subalgebra (𝓞 ℚ) (QuatF ℚ a b), IsMaximalOrder (𝓞 ℚ) ℚ O → ∀ n : ℕ, 1 ≤ n →
      brandtTrace O n =
        ∑ t ∈ (Finset.Icc (-(2 * n : ℤ)) (2 * n)).filter (fun t : ℤ => t ^ 2 < 4 * (n : ℤ)),
          modHurwitz (ramFin ha hb) (fun v => Ideal.absNorm v.asIdeal) (t ^ 2 - 4 * (n : ℤ)) +
        if IsSquare n then (∏ v ∈ ramFin ha hb, ((Ideal.absNorm v.asIdeal : ℝ) - 1)) / 12 else 0

/-! ## Consistency: the trace formula at $n = 1$ is the class number formula -/

/-- $T(1)$ is the identity matrix: $\operatorname{tr} T(1) = \# \operatorname{Cls}\mathcal O$ (the only subideal of
index $1$ of $I$ is $I$). -/
theorem brandtTrace_one {a b : 𝓞 ℚ} (O : Subalgebra (𝓞 ℚ) (QuatF ℚ a b)) :
    brandtTrace O 1 = Nat.card {c : Quotient (idealSetoid O) // c.out ≠ ⊥} := by
  have h1 : ∀ c : {c : Quotient (idealSetoid O) // c.out ≠ ⊥},
      (Set.ncard {J : Ideal O | J ≤ c.1.out ∧
        J.toAddSubgroup.relIndex c.1.out.toAddSubgroup = 1 ^ 2 ∧ (idealSetoid O) J c.1.out} : ℝ) = 1 := by
    intro c
    have : {J : Ideal O | J ≤ c.1.out ∧
        J.toAddSubgroup.relIndex c.1.out.toAddSubgroup = 1 ^ 2 ∧ (idealSetoid O) J c.1.out} =
        {c.1.out} := by
      ext J
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, one_pow, AddSubgroup.relIndex_eq_one]
      constructor
      · rintro ⟨h1, h2, -⟩
        exact le_antisymm h1 ((Submodule.toAddSubgroup_le _ _).1 h2)
      · rintro rfl
        exact ⟨le_rfl, le_rfl, (idealSetoid O).iseqv.refl _⟩
    rw [this, Set.ncard_singleton]
    simp
  unfold brandtTrace
  simp_rw [h1]
  by_cases hfin : Finite {c : Quotient (idealSetoid O) // c.out ≠ ⊥}
  · haveI := Fintype.ofFinite {c : Quotient (idealSetoid O) // c.out ≠ ⊥}
    rw [tsum_fintype, Finset.sum_const, Nat.card_eq_fintype_card]
    simp
  · haveI : Infinite {c : Quotient (idealSetoid O) // c.out ≠ ⊥} := not_finite_iff_infinite.mp hfin
    rw [Nat.card_eq_zero_of_infinite, tsum_eq_zero_of_not_summable]
    · simp
    · intro hs
      exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hs.tendsto_cofinite_zero)

/-- $h(-4) = 1$: the only reduced form of discriminant $-4$ is $x^2 + y^2$. -/
theorem formClassNumber_neg_four : formClassNumber (-4) = 1 := by
  unfold formClassNumber
  have : {f : ℤ × ℤ × ℤ | f.2.1 ^ 2 - 4 * f.1 * f.2.2 = -4 ∧
      Int.gcd (Int.gcd f.1 f.2.1 : ℤ) f.2.2 = 1 ∧ |f.2.1| ≤ f.1 ∧ f.1 ≤ f.2.2 ∧
      ((|f.2.1| = f.1 ∨ f.1 = f.2.2) → 0 ≤ f.2.1)} = {(1, 0, 1)} := by
    ext ⟨A, B, C⟩
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨hd, -, hB, hAC, -⟩
      have hA0 : 0 ≤ A := le_trans (abs_nonneg B) hB
      have hB2 : B ^ 2 ≤ A ^ 2 := by
        rw [← sq_abs B]; exact pow_le_pow_left₀ (abs_nonneg B) hB 2
      have hA1 : A ≤ 1 := by nlinarith
      have hBa : -1 ≤ B ∧ B ≤ 1 := abs_le.1 (le_trans hB hA1)
      obtain ⟨hBl, hBu⟩ := hBa
      interval_cases A <;> interval_cases B <;> omega
    · rintro ⟨rfl, rfl, rfl⟩
      refine ⟨by norm_num, by decide, by norm_num, le_rfl, fun _ => le_rfl⟩
  rw [this, Set.ncard_singleton]

/-- $h(-3) = 1$: the only reduced form of discriminant $-3$ is $x^2 + xy + y^2$. -/
theorem formClassNumber_neg_three : formClassNumber (-3) = 1 := by
  unfold formClassNumber
  have : {f : ℤ × ℤ × ℤ | f.2.1 ^ 2 - 4 * f.1 * f.2.2 = -3 ∧
      Int.gcd (Int.gcd f.1 f.2.1 : ℤ) f.2.2 = 1 ∧ |f.2.1| ≤ f.1 ∧ f.1 ≤ f.2.2 ∧
      ((|f.2.1| = f.1 ∨ f.1 = f.2.2) → 0 ≤ f.2.1)} = {(1, 1, 1)} := by
    ext ⟨A, B, C⟩
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨hd, -, hB, hAC, hcond⟩
      have hA0 : 0 ≤ A := le_trans (abs_nonneg B) hB
      have hB2 : B ^ 2 ≤ A ^ 2 := by
        rw [← sq_abs B]; exact pow_le_pow_left₀ (abs_nonneg B) hB 2
      have hA1 : A ≤ 1 := by nlinarith
      have hBa : -1 ≤ B ∧ B ≤ 1 := abs_le.1 (le_trans hB hA1)
      obtain ⟨hBl, hBu⟩ := hBa
      interval_cases A <;> interval_cases B <;> simp at hcond <;> omega
    · rintro ⟨rfl, rfl, rfl⟩
      refine ⟨by norm_num, by decide, by norm_num, le_rfl, fun _ => by norm_num⟩
  rw [this, Set.ncard_singleton]

/-- The local embedding factors of $\mathbb Z[i]$ and $\mathbb Z[\omega]$ at a prime $p \ge 2$:
$1 - \left(\frac{-4}{p}\right)$ and $1 - \left(\frac{-3}{p}\right)$ (both orders are maximal). -/
theorem localEmb_neg_four {p : ℕ} (hp : 2 ≤ p) : localEmb (-4) p = 1 - Siegel.kroneckerSym (-4) p := by
  unfold localEmb
  rw [if_neg]
  rintro ⟨hd, hD⟩
  have hle : ((p : ℤ) ^ 2) ≤ 4 := by
    have := Int.le_of_dvd (by norm_num) ((Int.dvd_neg).2 hd)
    simpa using this
  have hp2 : p = 2 := by
    have : (p : ℤ) ≤ 2 := by nlinarith
    omega
  subst hp2
  revert hD
  decide

theorem localEmb_neg_three {p : ℕ} (hp : 2 ≤ p) : localEmb (-3) p = 1 - Siegel.kroneckerSym (-3) p := by
  unfold localEmb
  rw [if_neg]
  rintro ⟨hd, -⟩
  have hle : ((p : ℤ) ^ 2) ≤ 3 := by
    have := Int.le_of_dvd (by norm_num) ((Int.dvd_neg).2 hd)
    simpa using this
  have : (2 : ℤ) ≤ p := by exact_mod_cast hp
  nlinarith

theorem modHurwitz_neg_four {ι : Type*} (P : Finset ι) (prime : ι → ℕ) (hP : ∀ v ∈ P, 2 ≤ prime v) :
    modHurwitz P prime (-4) = (∏ v ∈ P, (1 - (Siegel.kroneckerSym (-4) (prime v) : ℝ))) / 4 := by
  unfold modHurwitz
  rw [show Finset.Icc 1 (Int.natAbs (-4)) = {1, 2, 3, 4} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide)]
  norm_num [IsDiscr, formClassNumber_neg_four, unitCount]
  rw [div_eq_inv_mul, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [localEmb_neg_four (hP v hv)]
  push_cast; ring
  norm_num

theorem modHurwitz_neg_three {ι : Type*} (P : Finset ι) (prime : ι → ℕ) (hP : ∀ v ∈ P, 2 ≤ prime v) :
    modHurwitz P prime (-3) = (∏ v ∈ P, (1 - (Siegel.kroneckerSym (-3) (prime v) : ℝ))) / 6 := by
  unfold modHurwitz
  rw [show Finset.Icc 1 (Int.natAbs (-3)) = {1, 2, 3} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide)]
  norm_num [IsDiscr, formClassNumber_neg_three, unitCount]
  rw [div_eq_inv_mul, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [localEmb_neg_three (hP v hv)]
  push_cast; ring
  norm_num

/-- The norm of a height-one prime of $\mathbb Z_F$ is at least $2$. -/
theorem two_le_absNorm {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  omega

/-- **The trace formula at $n = 1$ gives the Eichler class number formula** (Voight Example 41.5.8,
(41.5.11), and Theorem 30.1.5): `BrandtTraceFormulaRat` implies `EichlerClassNumberFormulaRat`, since
$\operatorname{tr} T(1) = \#\operatorname{Cls}\mathcal O$ (`brandtTrace_one`) and
$\sum_{t^2 < 4} H_D(t^2 - 4) = H_D(-4) + 2H_D(-3) = \tfrac14\prod_{p \mid D}(1 - (\tfrac{-4}{p}))
+ \tfrac13\prod_{p \mid D}(1 - (\tfrac{-3}{p}))$ ($h(-4) = h(-3) = 1$, $\#\mathbb Z[i]^\times = 4$,
$\#\mathbb Z[\omega]^\times = 6$). A check that the two statements are consistent. -/
@[kb "voight2021" "Example 41.5.8, (41.5.11), p. 777"]
theorem eichlerClassNumberFormulaRat_of_brandtTraceFormulaRat (h : BrandtTraceFormulaRat) :
    EichlerClassNumberFormulaRat := by
  intro a b ha hb hdef O hO
  have := h a b ha hb hdef O hO 1 le_rfl
  rw [brandtTrace_one] at this
  rw [this]
  have hP : ∀ v ∈ ramFin ha hb, 2 ≤ Ideal.absNorm v.asIdeal := fun v _ => two_le_absNorm v
  rw [show ((Finset.Icc (-(2 * ((1 : ℕ) : ℤ))) (2 * ((1 : ℕ) : ℤ))).filter
      (fun t : ℤ => t ^ 2 < 4 * ((1 : ℕ) : ℤ))) = {-1, 0, 1} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide)]
  norm_num
  rw [modHurwitz_neg_four _ _ hP, modHurwitz_neg_three _ _ hP]
  ring

end QuadFormsKB.Voight
