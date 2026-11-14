/-
# Local densities over $\mathbb F_q(t)$: the headline local results at every finite place (function field case)

**Layer:** function field (statements for $Q$ = `QuadForm k[X] n` at a finite place $v = (P)$ of $k[X]$, $k$ finite
with $\operatorname{char} k \ne 2$). This is the function field port of `NFLocal.lean`.
**Defines** the local density $\beta_v(Q, m) = \lim_j r_{P^j}(m)/(Nv)^{j(n-1)}$ directly over $k[X]$
(`FF.localDensity`; $Nv = |k[X]/P| = q^{\deg P}$), the primitive density, the local constant $C_v$, and the notions
"locally represented" / "$v$-stable" over $k[X]$; each agrees with its discrete valuation ring counterpart at the completion
$\mathfrak o_v$ (`localDensity_eq_completion`, …). **Proves**, each as a short instantiation of the discrete valuation ring theory
through `FFDensityBridge.lean`: existence of $\beta_v$ (5.2); the corrected normal form (Lemma 2.1); Lemma 3.2;
Lemma 3.8 (corrected) and Cor. 3.8.2; (5.6), (5.7), (5.8), (5.10), (5.11) and $C_v > 0$. The uniformizer is the
global polynomial $\varpi$ = `unif v` $\in P \setminus P^2$. Isotropy is over the completion $F_v$ of
$F = k(t)$ (`RatFunc k`).

*Not ported:* the final section of `NFLocal.lean` (consistency with the rational theory for $F = \mathbb Q$,
`ratQuotEquiv`, `localDensity_rat`) is specific to $\mathcal O_{\mathbb Q} = \mathbb Z$ and has no function
field analogue here.

Hypothesis: `ringChar k ≠ 2` (named `hk`), used wherever the discrete valuation ring theory needs $2 \ne 0$ in $\mathfrak o_v$.
Indices are 0-based.
-/
import QuadFormsKB.FunctionField.FFDensityBridge

open IsDedekindDomain WithZero Filter Topology Polynomial

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.LocalDensity.FF

open QuadForm

variable {k : Type} [Field k] [Finite k] (v : HeightOneSpectrum k[X]) {n : ℕ}

local notation "Fv" => v.adicCompletion (RatFunc k)
local notation "𝔬" => v.adicCompletionIntegers (RatFunc k)
local notation "Nv" => (Nm v : ℝ)

/-! ### Isotropy over $F_v$ and diagonal forms -/

/-- Evaluating the base change $Q \otimes \mathfrak o_v$ in $F_v$ is evaluating $Q$ in $F_v$. -/
theorem evalIn_Qp (Q : QuadForm k[X] n) (x : Fin n → Fv) : (Qp v Q).evalIn Fv x = Q.evalIn Fv x := by
  have h : ∀ c : k[X], algebraMap 𝔬 Fv (ι v c) = algebraMap k[X] Fv c := fun _ => rfl
  simp only [QuadForm.evalIn, QuadForm.map, Matrix.map_apply, h]

/-- $Q \otimes \mathfrak o_v$ is isotropic over $F_v$ iff $Q$ is. -/
theorem isotropicIn_Qp_iff (Q : QuadForm k[X] n) : (Qp v Q).IsotropicIn Fv ↔ Q.IsotropicIn Fv := by
  simp only [QuadForm.IsotropicIn, evalIn_Qp]

/-- The base change of a diagonal form is diagonal. -/
theorem Qp_diag (a : Fin n → k[X]) : Qp v (QuadForm.diag a) = QuadForm.diag fun i => ι v (a i) := by
  ext i j
  simp only [QuadForm.map, QuadForm.diag, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

/-- $\varpi \mid \iota(a) \iff a \in P$. -/
theorem π_dvd_ι_iff (a : k[X]) : π v ∣ ι v a ↔ a ∈ v.asIdeal := by
  rw [← pow_one (π v), π_pow_dvd_ι_iff, pow_one]

/-! ### Densities over $k[X]$ -/

/-- **The local density $\beta_v(Q, m)$** over $k[X]$ (Hanke 2004, (5.1)–(5.2), p. 368, with the corrected
exponent; function field case): $\beta_v(m) = \lim_j r_{P^j}(m)/(Nv)^{j(n-1)}$. It equals the discrete valuation ring density at the
completion (`localDensity_eq_completion`); the limit exists for $Q$ nondegenerate and $m \ne 0$
(`localDensity_eventually_eq`). -/
@[kb "hanke2004" "(5.1)–(5.2), p. 368 (function field case)"]
def localDensity (Q : QuadForm k[X] n) (m : k[X]) : ℝ :=
  limUnder atTop fun j : ℕ => (repCount v Q j m : ℝ) / Nv ^ (j * (n - 1))

/-- **Primitive (non-Zero-type) local density** over $k[X]$ (Hanke 2004, Def. 5.1, p. 368; function field case):
$\beta^{\mathrm{Good}\cup\mathrm{Bad}}_v(m) = \lim_j r^{\mathrm{Good}\cup\mathrm{Bad}}_{P^j}(m)/(Nv)^{j(n-1)}$. -/
def localDensityPrim (Q : QuadForm k[X] n) (m : k[X]) : ℝ :=
  limUnder atTop fun j : ℕ =>
    (repCountOf v Q j m (fun x => ¬ IsZeroType v j x) : ℝ) / Nv ^ (j * (n - 1))

/-- **The local constant $C_v(T)$** (Hanke 2004, after (5.8), p. 370; function field case):
$C_v(T) = \frac{Nv^{n-2}}{Nv^{n-2} - 1} \cdot \frac{\beta^{\mathrm{Good}\cup\mathrm{Bad}}_v(\varpi^2 T)}{\beta_v(T)}$. -/
@[kb "hanke2004" "after (5.8), p. 370 (function field case)"]
def localConstC (Q : QuadForm k[X] n) (T : k[X]) : ℝ :=
  (Nv ^ (n - 2) / (Nv ^ (n - 2) - 1)) *
    (localDensityPrim v Q (unif v ^ 2 * T) / localDensity v Q T)

/-- $C'_v(T) = \min(1, C_v(T))$ (Hanke 2004, (5.11), p. 371; function field case). -/
def localConstC' (Q : QuadForm k[X] n) (T : k[X]) : ℝ := min 1 (localConstC v Q T)

/-- **Locally represented at $v$** (Hanke 2004, Def. 3.5, p. 362; function field case): $r_{P^j}(m) > 0$ for all
large $j$. -/
def IsLocallyRepresentedAt (Q : QuadForm k[X] n) (m : k[X]) : Prop :=
  ∀ᶠ j in atTop, 0 < repCount v Q j m

/-- **$v$-stable** (Hanke 2004, Def. 3.6, p. 362; function field case): $m$ is locally represented at $v$, and for
all large $j$ the number of non-Zero-type solutions mod $P^j$ of $Q = \varpi^{2\nu} m$ is the same for
every $\nu \ge 1$. -/
@[kb "hanke2004" "Def. 3.6, p. 362 (function field case)"]
def IsPStable (Q : QuadForm k[X] n) (m : k[X]) : Prop :=
  IsLocallyRepresentedAt v Q m ∧
    ∀ᶠ j in atTop, ∀ ν ≥ 1,
      repCountOf v Q j (unif v ^ (2 * ν) * m) (fun x => ¬ IsZeroType v j x) =
        repCountOf v Q j (unif v ^ 2 * m) (fun x => ¬ IsZeroType v j x)

/-! ### Agreement with the completion -/

theorem localDensity_eq_completion (Q : QuadForm k[X] n) (m : k[X]) :
    localDensity v Q m = DVR.localDensity (Qp v Q) (π v) (ι v m) := by
  simp only [localDensity, DVR.localDensity, repCount_eq_completion, q_completion]

theorem localDensityPrim_eq_completion (Q : QuadForm k[X] n) (m : k[X]) :
    localDensityPrim v Q m =
      DVR.localDensityOf (Qp v Q) (π v) (ι v m) (fun j x => ¬ DVR.IsZeroType (π v) j x) := by
  simp only [localDensityPrim, DVR.localDensityOf, repCountNonZero_eq_completion, q_completion]

theorem localConstC_eq_completion (Q : QuadForm k[X] n) (T : k[X]) :
    localConstC v Q T = DVR.localConstC (Qp v Q) (π v) (ι v T) := by
  simp only [localConstC, DVR.localConstC, localDensityPrim_eq_completion, localDensity_eq_completion,
    q_completion, map_mul, map_pow]

theorem localConstC'_eq_completion (Q : QuadForm k[X] n) (T : k[X]) :
    localConstC' v Q T = DVR.localConstC' (Qp v Q) (π v) (ι v T) := by
  simp only [localConstC', DVR.localConstC', localConstC_eq_completion]

theorem isLocallyRepresentedAt_iff (Q : QuadForm k[X] n) (m : k[X]) :
    IsLocallyRepresentedAt v Q m ↔ DVR.IsLocallyRepresentedAt (Qp v Q) (π v) (ι v m) := by
  simp only [IsLocallyRepresentedAt, DVR.IsLocallyRepresentedAt, repCount_eq_completion]

theorem isPStable_iff (Q : QuadForm k[X] n) (S₀ : Finset (Fin n)) (m : k[X]) :
    IsPStable v Q m ↔ DVR.IsPStable (Qp v Q) S₀ (π v) (ι v m) := by
  simp only [IsPStable, DVR.IsPStable, isLocallyRepresentedAt_iff, repCountNonZero_eq_completion,
    map_mul, map_pow]

/-! ### The headline local results over $F = k(t)$ -/

/-- **Existence of $\beta_v$ at every finite place** (Hanke 2004, (5.2), p. 368; function field case): for $Q$
nondegenerate over $k[X]$ and $m \ne 0$, the normalized counts $r_{P^j}(m)/(Nv)^{j(n-1)}$ are eventually equal to
$\beta_v(Q, m)$. From `DVR.localDensity_eventually_eq`. -/
@[kb "hanke2004" "(5.2), p. 368 (function field case)"]
theorem localDensity_eventually_eq (hk : ringChar k ≠ 2) (Q : QuadForm k[X] n) (hQ : Q.Nondegenerate)
    (m : k[X]) (hm : m ≠ 0) :
    ∀ᶠ j in atTop, (repCount v Q j m : ℝ) / Nv ^ (j * (n - 1)) = localDensity v Q m := by
  have h := DVR.localDensity_eventually_eq (Qp v Q) (nondegenerate_Qp v hQ) (π v) (irreducible_π v)
    (ι v m) (ι_ne_zero v hm) (two_ne_zero' v hk)
  simpa only [← repCount_eq_completion, q_completion, ← localDensity_eq_completion] using h

/-- **The limit defining $\beta_v(Q, m)$ exists** (Hanke 2004, (5.2), p. 368; function field case). -/
@[kb "hanke2004" "(5.2), p. 368 (function field case)"]
theorem tendsto_localDensity (hk : ringChar k ≠ 2) (Q : QuadForm k[X] n) (hQ : Q.Nondegenerate)
    (m : k[X]) (hm : m ≠ 0) :
    Tendsto (fun j : ℕ => (repCount v Q j m : ℝ) / Nv ^ (j * (n - 1))) atTop
      (𝓝 (localDensity v Q m)) :=
  tendsto_const_nhds.congr' (by
    filter_upwards [localDensity_eventually_eq v hk Q hQ m hm] with j hj using hj.symm)

/-- **Local normal form over $\mathfrak o_v$, corrected** (Hanke 2004, Lemma 2.1, p. 355, corrected;
function field case): every nondegenerate $Q$ over $k[X]$ has the counts mod $P^j$
of a form $Q'$ over $\mathfrak o_v$ in the general normal form `IsJordanFormW`, with no 2-dimensional blocks when
$v \nmid 2$. From `DVR.exists_jordanFormW`. -/
@[kb "hanke2004" "Lemma 2.1, p. 355 (corrected) (function field case)"]
theorem exists_jordanFormW (hk : ringChar k ≠ 2) (Q : QuadForm k[X] n) (hQ : Q.Nondegenerate) :
    ∃ (Q' : QuadForm 𝔬 n) (P : Finset (Fin n × Fin n)) (w : Fin n → ℕ),
      DVR.IsJordanFormW Q' (π v) P w ∧ ((2 : k[X]) ∉ v.asIdeal → P = ∅) ∧
        ∀ j m, repCount v Q j m = DVR.repCount Q' (π v) j (ι v m) := by
  obtain ⟨Q', P, w, hJ, hP, hc⟩ :=
    DVR.exists_jordanFormW (Qp v Q) (nondegenerate_Qp v hQ) (π v) (irreducible_π v) (two_ne_zero' v hk)
  refine ⟨Q', P, w, hJ, fun h2 => hP ?_, fun j m => by rw [repCount_eq_completion, hc]⟩
  rwa [← pow_one (π v), π_pow_dvd_two_iff, pow_one]

/-- **Local normal form as printed, when $P^2 \nmid 2$** (Hanke 2004, Lemma 2.1, p. 355; function field case): then
the printed normal form `DVR.IsJordanForm` exists over $\mathfrak o_v$, with the counts of $Q$. From
`DVR.exists_jordanForm`. -/
@[kb "hanke2004" "Lemma 2.1, p. 355 (function field case)"]
theorem exists_jordanForm (Q : QuadForm k[X] n) (hQ : Q.Nondegenerate)
    (h2 : (2 : k[X]) ∉ v.asIdeal ^ 2) :
    ∃ (Q' : QuadForm 𝔬 n) (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ),
      DVR.IsJordanForm Q' (π v) P ν ∧ ((2 : k[X]) ∉ v.asIdeal → P = ∅) ∧
        ∀ j m, repCount v Q j m = DVR.repCount Q' (π v) j (ι v m) := by
  obtain ⟨Q', P, ν, hJ, hP, hc⟩ := DVR.exists_jordanForm (Qp v Q) (nondegenerate_Qp v hQ) (π v)
    (irreducible_π v) (by rwa [π_pow_dvd_two_iff])
  refine ⟨Q', P, ν, hJ, fun h2 => hP ?_, fun j m => by rw [repCount_eq_completion, hc]⟩
  rwa [← pow_one (π v), π_pow_dvd_two_iff, pow_one]

/-- **The printed and the corrected normal forms agree when $P^2 \nmid 2$** (Hanke 2004, Lemma 2.1, p. 355;
function field case). From `DVR.isJordanForm_iff_isJordanFormW`. -/
@[kb "hanke2004" "Lemma 2.1, p. 355 (function field case)"]
theorem isJordanForm_iff_isJordanFormW (h2 : (2 : k[X]) ∉ v.asIdeal ^ 2) {Q' : QuadForm 𝔬 n}
    {P : Finset (Fin n × Fin n)} {ν : Fin n → ℕ} :
    DVR.IsJordanForm Q' (π v) P ν ↔ DVR.IsJordanFormW Q' (π v) P ν :=
  DVR.isJordanForm_iff_isJordanFormW (irreducible_π v) (by rwa [π_pow_dvd_two_iff])

/-- **Lemma 3.2 over $F = k(t)$** (Hanke 2004, Lemma 3.2, eq. (3.1), p. 358; function field case): if
$Q \otimes \mathfrak o_v$ is in normal form with gradient bound $t$, then for $j \ge 2t + 1$ and $l \ge 0$,
$r^{\mathrm{Good}}_{P^{j+l}}(m) = (Nv)^{(n-1)l}\, r^{\mathrm{Good}}_{P^j}(m)$ (Good type relative to the
unimodular coordinates). From `DVR.repCountGood_add_of_gradBound`. -/
@[kb "hanke2004" "Lemma 3.2, eq. (3.1), p. 358 (function field case)"]
theorem repCountGood_add_of_gradBound (Q : QuadForm k[X] n) (P : Finset (Fin n × Fin n))
    (w : Fin n → ℕ) (hJ : DVR.IsJordanFormW (Qp v Q) (π v) P w) (t : ℕ)
    (hB : DVR.GradBound (Qp v Q) (π v) P w t) (m : k[X]) (j l : ℕ) (hj : 2 * t + 1 ≤ j) :
    repCountOf v Q (j + l) m (IsGoodType v (unimodularCoords w) (j + l)) =
      Nm v ^ ((n - 1) * l) *
        repCountOf v Q j m (IsGoodType v (unimodularCoords w) j) := by
  rw [repCountGood_eq_completion, repCountGood_eq_completion,
    DVR.repCountGood_add_of_gradBound _ _ (irreducible_π v) P w hJ t hB _ j l hj, q_completion]

/-- **Lemma 3.2 over $F = k(t)$ with $t = \mathrm{ord}_v(2)$** (Hanke 2004, Lemma 3.2, eq. (3.1), p. 358; function
field case): for $Q \otimes \mathfrak o_v$ in normal form, $2 \in P^e \setminus P^{e+1}$, $j \ge 2e + 1$:
$r^{\mathrm{Good}}_{P^{j+l}}(m) = (Nv)^{(n-1)l}\, r^{\mathrm{Good}}_{P^j}(m)$. From `DVR.repCountGood_add`. -/
@[kb "hanke2004" "Lemma 3.2, eq. (3.1), p. 358 (function field case)"]
theorem repCountGood_add (Q : QuadForm k[X] n) (P : Finset (Fin n × Fin n)) (w : Fin n → ℕ)
    (hJ : DVR.IsJordanFormW (Qp v Q) (π v) P w) (e : ℕ)
    (he : (2 : k[X]) ∈ v.asIdeal ^ e ∧ (2 : k[X]) ∉ v.asIdeal ^ (e + 1)) (m : k[X]) (j l : ℕ)
    (hj : 2 * e + 1 ≤ j) :
    repCountOf v Q (j + l) m (IsGoodType v (unimodularCoords w) (j + l)) =
      Nm v ^ ((n - 1) * l) *
        repCountOf v Q j m (IsGoodType v (unimodularCoords w) j) := by
  rw [repCountGood_eq_completion, repCountGood_eq_completion,
    DVR.repCountGood_add _ _ (irreducible_π v) P w hJ e
      ⟨(π_pow_dvd_two_iff v e).mpr he.1, fun h => he.2 ((π_pow_dvd_two_iff v _).mp h)⟩ _ j l hj,
    q_completion]

/-- **Lemma 3.8 over $F = k(t)$, corrected** (Hanke 2004, Lemma 3.8, p. 363, corrected; function field case): for
$m$ $v$-stable, $Q$ is anisotropic over $F_v$ iff eventually every solution of $Q \equiv \varpi^2 m \pmod{P^j}$ is
of Zero type. From `DVR.anisotropic_iff_zeroType` (which needs `isAdicComplete`). -/
@[kb "hanke2004" "Lemma 3.8, p. 363 (corrected) (function field case)"]
theorem anisotropic_iff_zeroType (Q : QuadForm k[X] n) (m : k[X]) (hm : IsPStable v Q m) :
    ¬ Q.IsotropicIn Fv ↔
      ∀ᶠ j in atTop,
        repCount v Q j (unif v ^ 2 * m) = repCountOf v Q j (unif v ^ 2 * m) (IsZeroType v j) := by
  have h := DVR.anisotropic_iff_zeroType Fv (Qp v Q) (π v) (irreducible_π v) ∅ (ι v m)
    ((isPStable_iff v Q ∅ m).mp hm)
  rw [isotropicIn_Qp_iff] at h
  simpa only [repCount_eq_completion, repCountZero_eq_completion, map_mul, map_pow] using h

/-- **Cor. 3.8.2 over $F = k(t)$, for a principal place** (Hanke 2004, Cor. 3.8.2, p. 364; function field case):
if $v = (p)$ (always true for $k[X]$, a principal ideal domain, with $p$ the monic irreducible polynomial of $v$), $Q$ is anisotropic
over $F_v$ and $m$ is $p$-stable (at the completion), then $Q$ has as many global solutions
$\vec x \in k[X]^n$ of $Q(\vec x) = p^{2e} m$ as of $Q(\vec x) = m$.
*Hypothesis:* the principality $v = (p)$ is what lets the global equation see $p$; the discrete valuation ring statement asks for
$A \ni p$ with $\varpi \mid \varphi(a) \Rightarrow p \mid a$. From `DVR.card_rep_mul_pow_sq`. -/
@[kb "hanke2004" "Cor. 3.8.2, p. 364 (function field case)"]
theorem card_rep_mul_pow_sq (p : k[X]) (hp : v.asIdeal = Ideal.span {p}) (Q : QuadForm k[X] n)
    (S₀ : Finset (Fin n)) (haniso : ¬ Q.IsotropicIn Fv) (m : k[X])
    (hm : DVR.IsPStable (Qp v Q) S₀ (ι v p) (ι v m)) (e : ℕ) :
    Set.ncard {x : Fin n → k[X] | Q.eval x = p ^ (2 * e) * m} =
      Set.ncard {x : Fin n → k[X] | Q.eval x = m} := by
  have hp1 : p ∈ v.asIdeal ^ 1 := by rw [pow_one, hp]; exact Ideal.mem_span_singleton_self p
  have hp2 : p ∉ v.asIdeal ^ 2 := by
    intro h
    have hu : unif v ∈ v.asIdeal := by
      rw [← v.intValuation_lt_one_iff_mem, intValuation_unif, ← exp_zero, exp_lt_exp]; omega
    rw [hp, Ideal.mem_span_singleton] at hu
    have hu2 : unif v ∈ v.asIdeal ^ 2 := Ideal.mem_of_dvd _ hu h
    have := (v.intValuation_le_pow_iff_mem _ 2).mpr hu2
    rw [intValuation_unif, exp_le_exp] at this
    omega
  have hval : Valued.v ((ι v p : 𝔬) : Fv) = exp (-1 : ℤ) := by
    rw [valued_ι]
    have h1 := (v.intValuation_le_pow_iff_mem p 1).mpr hp1
    have h2 := mt (v.intValuation_le_pow_iff_mem p 2).mp hp2
    have h0 : v.intValuation p ≠ 0 := by
      have hp0 : p ≠ 0 := fun h => v.ne_bot (by rw [hp, h, Ideal.span_singleton_eq_bot.mpr rfl])
      rw [v.intValuation_if_neg hp0]; exact exp_ne_zero
    rw [← exp_log h0] at h1 h2 ⊢
    rw [exp_le_exp] at h1 h2
    rw [exp_inj]; push_cast at h1 h2; omega
  have hirr : Irreducible (ι v p) := irreducible_of_valued v hval
  have hA : ∀ a : k[X], ι v p ∣ ι v a → p ∣ a := by
    intro a ha
    have hass : Associated (π v) (ι v p) :=
      IsDiscreteValuationRing.associated_of_irreducible _ (irreducible_π v) hirr
    rw [← Ideal.mem_span_singleton, ← hp, ← π_dvd_ι_iff]
    exact hass.dvd.trans ha
  have h := DVR.card_rep_mul_pow_sq Fv (ι v) Q p (ι v p) hirr rfl hA S₀
    (by rwa [← Qp, isotropicIn_Qp_iff]) m hm e
  exact h

/-- **(5.6) over $F = k(t)$** (Hanke 2004, (5.6), p. 369; function field case): for $n \ge 3$, $Q$ nondegenerate,
$m \ne 0$: $\beta_v(m) \le (Nv)^{n-2}\, \beta_v(\varpi^2 m)$. From `DVR.localDensity_le_mul_sq`. -/
@[kb "hanke2004" "(5.6), p. 369 (function field case)"]
theorem localDensity_le_mul_sq (hk : ringChar k ≠ 2) (Q : QuadForm k[X] n) (hQ : Q.Nondegenerate)
    (hn : 3 ≤ n) (m : k[X]) (hm : m ≠ 0) :
    localDensity v Q m ≤ Nv ^ (n - 2) * localDensity v Q (unif v ^ 2 * m) := by
  have h := DVR.localDensity_le_mul_sq (Qp v Q) (nondegenerate_Qp v hQ) hn (π v) (irreducible_π v)
    (two_ne_zero' v hk) (ι v m) (ι_ne_zero v hm)
  simpa only [localDensity_eq_completion, q_completion, map_mul, map_pow] using h

/-- **(5.7) over $F = k(t)$** (Hanke 2004, (5.7), p. 369; function field case): for $Q$ nondegenerate and isotropic
over $F_v$ and $T \ne 0$ $v$-stable,
$\beta_v(\varpi^{2e} T) = \beta^{\mathrm{Good}\cup\mathrm{Bad}}_v(\varpi^2 T) \sum_{i<e} (Nv^{n-2})^{-i} +
\beta_v(T)/(Nv)^{(n-2)e}$. From `DVR.localDensity_pow_sq`. -/
@[kb "hanke2004" "(5.7), p. 369 (function field case)"]
theorem localDensity_pow_sq (hk : ringChar k ≠ 2) (Q : QuadForm k[X] n) (hQ : Q.Nondegenerate)
    (hiso : Q.IsotropicIn Fv) (T : k[X]) (hT0 : T ≠ 0) (hT : IsPStable v Q T) (e : ℕ) :
    localDensity v Q (unif v ^ (2 * e) * T) =
      localDensityPrim v Q (unif v ^ 2 * T) * ∑ i ∈ Finset.range e, (Nv ^ (n - 2))⁻¹ ^ i +
        localDensity v Q T / Nv ^ ((n - 2) * e) := by
  have h := DVR.localDensity_pow_sq Fv (Qp v Q) (nondegenerate_Qp v hQ) (π v) (irreducible_π v)
    (two_ne_zero' v hk) ∅ ((isotropicIn_Qp_iff v Q).mpr hiso) (ι v T) (ι_ne_zero v hT0)
    ((isPStable_iff v Q ∅ T).mp hT) e
  simpa only [localDensity_eq_completion, localDensityPrim_eq_completion, q_completion, map_mul,
    map_pow] using h

/-- **(5.8) over $F = k(t)$** (Hanke 2004, (5.8), p. 369; function field case): for $n \ge 3$, $Q$ nondegenerate,
$T \ne 0$ $v$-stable:
$\beta_v(\varpi^{2\nu} T)/\beta_v(T) = C_v(T) + (1 - C_v(T))/(Nv)^{(n-2)\nu}$. From
`DVR.localDensity_pow_sq_div`. -/
@[kb "hanke2004" "(5.8), p. 369 (function field case)"]
theorem localDensity_pow_sq_div (hk : ringChar k ≠ 2) (Q : QuadForm k[X] n) (hQ : Q.Nondegenerate)
    (hn : 3 ≤ n) (T : k[X]) (hT0 : T ≠ 0) (hT : IsPStable v Q T) (ν : ℕ) :
    localDensity v Q (unif v ^ (2 * ν) * T) / localDensity v Q T =
      localConstC v Q T + (1 - localConstC v Q T) / Nv ^ ((n - 2) * ν) := by
  have h := DVR.localDensity_pow_sq_div (Qp v Q) (nondegenerate_Qp v hQ) hn (π v) (irreducible_π v)
    (two_ne_zero' v hk) ∅ (ι v T) (ι_ne_zero v hT0) ((isPStable_iff v Q ∅ T).mp hT) ν
  simpa only [localDensity_eq_completion, localConstC_eq_completion, q_completion, map_mul,
    map_pow] using h

/-- **$C_v > 0$ for isotropic $Q$** (Hanke 2004, proof of Thm 5.4, p. 370; function field case): for $n \ge 3$,
$Q$ nondegenerate and isotropic over $F_v$, $T \ne 0$ $v$-stable, $C_v(T) > 0$. From
`DVR.localConstC_pos` (which needs `isAdicComplete`). -/
@[kb "hanke2004" "Proof of Thm 5.4, p. 370 (C_p > 0) (function field case)"]
theorem localConstC_pos (hk : ringChar k ≠ 2) (Q : QuadForm k[X] n) (hQ : Q.Nondegenerate)
    (hn : 3 ≤ n) (hiso : Q.IsotropicIn Fv) (T : k[X]) (hT0 : T ≠ 0) (hT : IsPStable v Q T) :
    0 < localConstC v Q T := by
  rw [localConstC_eq_completion]
  exact DVR.localConstC_pos Fv (Qp v Q) (nondegenerate_Qp v hQ) hn (π v) (irreducible_π v)
    (two_ne_zero' v hk) ∅ ((isotropicIn_Qp_iff v Q).mpr hiso) (ι v T) (ι_ne_zero v hT0)
    ((isPStable_iff v Q ∅ T).mp hT)

/-- **(5.11) over $F = k(t)$** (Hanke 2004, (5.11), p. 371; function field case): for $n \ge 3$, $Q$ nondegenerate,
$T \ne 0$ $v$-stable: $C'_v(T)\, \beta_v(T) \le \beta_v(\varpi^{2\nu} T)$. From `DVR.localDensity_pow_sq_ge`. -/
@[kb "hanke2004" "(5.11), p. 371 (function field case)"]
theorem localDensity_pow_sq_ge (hk : ringChar k ≠ 2) (Q : QuadForm k[X] n) (hQ : Q.Nondegenerate)
    (hn : 3 ≤ n) (T : k[X]) (hT0 : T ≠ 0) (hT : IsPStable v Q T) (ν : ℕ) :
    localConstC' v Q T * localDensity v Q T ≤ localDensity v Q (unif v ^ (2 * ν) * T) := by
  have h := DVR.localDensity_pow_sq_ge (Qp v Q) (nondegenerate_Qp v hQ) hn (π v) (irreducible_π v)
    (two_ne_zero' v hk) ∅ (ι v T) (ι_ne_zero v hT0) ((isPStable_iff v Q ∅ T).mp hT) ν
  simpa only [localDensity_eq_completion, localConstC'_eq_completion, map_mul, map_pow] using h

/-- **(5.11) over $F = k(t)$, ratio form** (Hanke 2004, (5.11), p. 371; function field case):
$C'_v(T) \le \beta_v(\varpi^{2\nu} T)/\beta_v(T)$. From `DVR.localDensity_pow_sq_div_ge`. -/
@[kb "hanke2004" "(5.11), p. 371 (function field case)"]
theorem localDensity_pow_sq_div_ge (hk : ringChar k ≠ 2) (Q : QuadForm k[X] n) (hQ : Q.Nondegenerate)
    (hn : 3 ≤ n) (T : k[X]) (hT0 : T ≠ 0) (hT : IsPStable v Q T) (ν : ℕ) :
    localConstC' v Q T ≤ localDensity v Q (unif v ^ (2 * ν) * T) / localDensity v Q T := by
  have h := DVR.localDensity_pow_sq_div_ge (Qp v Q) (nondegenerate_Qp v hQ) hn (π v)
    (irreducible_π v) (two_ne_zero' v hk) ∅ (ι v T) (ι_ne_zero v hT0) ((isPStable_iff v Q ∅ T).mp hT) ν
  simpa only [localDensity_eq_completion, localConstC'_eq_completion, map_mul, map_pow] using h

/-- **(5.10) over $F = k(t)$** (Hanke 2004, (5.10), p. 371; function field case): for a ternary diagonal form
$\langle a_0, a_1, a_2\rangle$ over $k[X]$ with unit coefficients at a place $v \nmid 2$, the factor
$C_v + (1 - C_v)/(Nv)^\nu$ is $1$ if $T \notin P$ and $-a_0a_1a_2T$ is a square mod $P$;
$(Nv^\nu + 2\sum_{\mu<\nu} Nv^\mu)/Nv^\nu$ if it is a non-square; and
$\sum_{\mu \le \nu} Nv^\mu / Nv^\nu$ if $T \in P \setminus P^2$. The quadratic character is that of
the residue field of $\mathfrak o_v$. From `DVR.eq_5_10`. -/
@[kb "hanke2004" "(5.10), p. 371 (function field case)"]
theorem eq_5_10 (a : Fin 3 → k[X]) (h2 : (2 : k[X]) ∉ v.asIdeal) (ha : ∀ i, a i ∉ v.asIdeal)
    (T : k[X]) (ν : ℕ) :
    let C := localConstC v (QuadForm.diag a) T
    let ψ := quadraticChar (IsLocalRing.ResidueField 𝔬)
      (IsLocalRing.residue 𝔬 (ι v (-(∏ i, a i) * T)))
    (T ∉ v.asIdeal → ψ = 1 → C + (1 - C) / Nv ^ ν = 1) ∧
    (T ∉ v.asIdeal → ψ = -1 →
      C + (1 - C) / Nv ^ ν = (Nv ^ ν + 2 * ∑ μ ∈ Finset.range ν, Nv ^ μ) / Nv ^ ν) ∧
    (T ∈ v.asIdeal → T ∉ v.asIdeal ^ 2 →
      C + (1 - C) / Nv ^ ν = (∑ μ ∈ Finset.range (ν + 1), Nv ^ μ) / Nv ^ ν) := by
  intro C ψ
  have h := DVR.eq_5_10 (fun i => ι v (a i)) (π v) (irreducible_π v)
    (by rwa [← map_ofNat (ι v), π_dvd_ι_iff]) (fun i => by rw [π_dvd_ι_iff]; exact ha i) (ι v T) ν
  simp only [← Qp_diag, ← localConstC_eq_completion, q_completion, π_dvd_ι_iff,
    π_pow_dvd_ι_iff] at h
  have hψ : ψ = quadraticChar (IsLocalRing.ResidueField 𝔬)
      (IsLocalRing.residue 𝔬 (-(∏ i, ι v (a i)) * ι v T)) := by
    simp only [ψ, map_mul, map_neg, map_prod]
  rw [hψ]
  exact h

end QuadFormsKB.LocalDensity.FF
