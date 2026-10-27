/-
# Local densities over a number field at dyadic $\mathfrak p \mid N$: explicit formulas
**Layer:** number field ($Q$ = `QuadForm (𝓞 F) n` at a finite prime $\mathfrak p$ = `v`, uniformizer $\varpi$ = `unif v`,
$e = \mathrm{ord}_\mathfrak p 2$ = `NF.ordTwo v`, $K_0 = \mathrm{ord}_\mathfrak p(4N) + 1$ = `NF.depthLevel v Q`). Instantiates
`DyadicClosed.lean` and `DyadicBad.lean` at $\mathfrak o_\mathfrak p$ through `NFBridge.lean`, at **every** prime, in particular at
dyadic $\mathfrak p \mid N$ of any ramification:

* `NF.localDensity_eq_level`: $\beta_\mathfrak p(m) = r_{\mathfrak p^K}(m)/(N\mathfrak p)^{K(n-1)}$ for $m \notin \mathfrak p^{a+1}$ and every
  $K \ge a + K_0$ — a count in $(\mathcal O_F/\mathfrak p^K)^n$;
* `NF.localDensity_eq_dyadicFormula`: $\beta_\mathfrak p(m) = \sum_{j \le a/2} (N\mathfrak p)^{j(2-n)}\beta^*_K(m/\varpi^{2j})$
  (`DVR.dyadicFormula` of $Q \otimes \mathfrak o_\mathfrak p$, $\mathrm{ord}_\mathfrak p m = a$, $K \ge K_0$);
* `NF.localDensity_unit_eq_level`: $\beta_\mathfrak p(m) = r_{\mathfrak p^{2e+1}}(m)/(N\mathfrak p)^{(2e+1)(n-1)}$ for $m \notin \mathfrak p$, every $Q$;
* `NF.localDensity_unit_diag`: unit diagonal forms at level $2e + 1$;
* `NF.localDensity_unary_unit`, `NF.localDensity_unary`: the closed form for $u x^2$ at dyadic $\mathfrak p$,
  $\beta_\mathfrak p(m) = 2(N\mathfrak p)^{e + a/2}$ if $a$ is even and $m/u$ is a square in $F_\mathfrak p$, else $0$
  (`NF.isSquare_div_iff`: square in $F_\mathfrak p$ = square in $\mathfrak o_\mathfrak p$ for units).

**Depends on** `NFDepth.lean`, `DyadicBad.lean`.
-/
import QuadFormsKB.LocalDensity.NFDepth
import QuadFormsKB.LocalDensity.DyadicBad

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.LocalDensity.NF

open QuadForm

variable {F : Type*} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "N𝔭" => (Ideal.absNorm v.asIdeal : ℝ)

/-- **$\beta_\mathfrak p(m)$ as a finite count at an explicit level, every prime** (Hanke 2004, (5.2), p. 368, with Lemma 3.4,
p. 361): for $Q$ nondegenerate over $\mathcal O_F$, $m \notin \mathfrak p^{a+1}$ and every $K \ge a + \mathrm{ord}_\mathfrak p(4N) + 1$,
$\beta_\mathfrak p(m) = r_{\mathfrak p^K}(m)/(N\mathfrak p)^{K(n-1)}$. From `DVR.localDensity_eq_level`. -/
@[kb "hanke2004" "(5.2), p. 368; Lemma 3.4, p. 361 (explicit level, over F)"]
theorem localDensity_eq_level (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) {a : ℕ} {m : 𝓞 F}
    (ha : m ∉ v.asIdeal ^ (a + 1)) (K : ℕ) (hK : a + depthLevel v Q ≤ K) :
    localDensity v Q m = (repCount v Q K m : ℝ) / N𝔭 ^ (K * (n - 1)) := by
  have ha' : ¬ π v ^ (a + 1) ∣ ι v m := by rwa [π_pow_dvd_ι_iff]
  rw [localDensity_eq_completion, DVR.localDensity_eq_level _ (nondegenerate_Qp v hQ) _ (irreducible_π v)
    (two_ne_zero' v) _ (ordTwo_spec v) ha' K hK, ← repCount_eq_completion, q_completion]

/-- **$\beta_\mathfrak p(m)$ by the dyadic formula, every prime** (Hanke 2004, §3 and (5.7), p. 369, without stability; the
explicit form of p. 362's "case-by-case basis" at $\mathfrak p \mid 2$): for $m \in \mathfrak p^a \setminus \mathfrak p^{a+1}$ and
$K \ge \mathrm{ord}_\mathfrak p(4N) + 1$, $\beta_\mathfrak p(m) = \sum_{j=0}^{\lfloor a/2\rfloor}(N\mathfrak p)^{j(2-n)}\,
r^{\mathrm{Good}\cup\mathrm{Bad}}_{\varpi^K}(m/\varpi^{2j})/(N\mathfrak p)^{K(n-1)}$, computed for $Q \otimes \mathfrak o_\mathfrak p$
(`DVR.dyadicFormula`). From `DVR.localDensity_eq_dyadicFormula`. -/
@[kb "hanke2004" "§3, (5.7), p. 369 (explicit, over F)"]
theorem localDensity_eq_dyadicFormula (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (K : ℕ)
    (hK : depthLevel v Q ≤ K) {a : ℕ} {m : 𝓞 F} (hda : m ∈ v.asIdeal ^ a) (ha : m ∉ v.asIdeal ^ (a + 1)) :
    localDensity v Q m = DVR.dyadicFormula (Qp v Q) (π v) K a (ι v m) := by
  rw [localDensity_eq_completion]
  exact DVR.localDensity_eq_dyadicFormula _ (nondegenerate_Qp v hQ) _ (irreducible_π v) (two_ne_zero' v) _
    (ordTwo_spec v) K hK ((π_pow_dvd_ι_iff v a m).2 hda) (by rwa [π_pow_dvd_ι_iff])

/-- **Unit densities at level $2e + 1$ for every nondegenerate $Q$ over $\mathcal O_F$, every prime** (Hanke 2004,
Remark 3.4.1(a), p. 361, and "solutions mod $4\mathfrak p$", p. 362, at every dyadic $\mathfrak p$, also $\mathfrak p \mid N$): for
$m \notin \mathfrak p$, $\beta_\mathfrak p(m) = r_{\mathfrak p^{2e+1}}(m)/(N\mathfrak p)^{(2e+1)(n-1)}$. From `DVR.localDensity_unit_eq_level`. -/
@[kb "hanke2004" "Remark 3.4.1(a), p. 361; p. 362 (\"mod 4𝔭\", over F)"]
theorem localDensity_unit_eq_level (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) {m : 𝓞 F}
    (hm : m ∉ v.asIdeal) :
    localDensity v Q m =
      (repCount v Q (2 * ordTwo v + 1) m : ℝ) / N𝔭 ^ ((2 * ordTwo v + 1) * (n - 1)) := by
  rw [localDensity_eq_completion, DVR.localDensity_unit_eq_level _ (nondegenerate_Qp v hQ) _ (irreducible_π v)
    (two_ne_zero' v) _ (ordTwo_spec v) (by rwa [π_dvd_ι_iff]) _ le_rfl, ← repCount_eq_completion, q_completion]

/-- **Unit densities of unit diagonal forms at level $2e + 1$, every prime** (Hanke 2004, Remark 3.4.1(a), p. 361 and
Lemma 3.2): for $u_i, m \notin \mathfrak p$, $\beta_\mathfrak p(\langle u\rangle, m) = r_{\mathfrak p^{2e+1}}(m)/(N\mathfrak p)^{(2e+1)(n-1)}$,
$e = \mathrm{ord}_\mathfrak p 2$. From `DVR.localDensity_unit_diag`. -/
@[kb "hanke2004" "Remark 3.4.1(a), p. 361 (dyadic 1-dimensional blocks, over F)"]
theorem localDensity_unit_diag (u : Fin n → 𝓞 F) (hu : ∀ i, u i ∉ v.asIdeal) {m : 𝓞 F} (hm : m ∉ v.asIdeal) :
    localDensity v (QuadForm.diag u) m =
      (repCount v (QuadForm.diag u) (2 * ordTwo v + 1) m : ℝ) / N𝔭 ^ ((2 * ordTwo v + 1) * (n - 1)) := by
  rw [localDensity_eq_completion, Qp_diag, DVR.localDensity_unit_diag _ _ (irreducible_π v)
    (fun i => by rw [π_dvd_ι_iff]; exact hu i) _ (ordTwo_spec v) (by rwa [π_dvd_ι_iff]), ← Qp_diag,
    ← repCount_eq_completion, q_completion]

/-- The base change of $\langle u\rangle$. -/
theorem Qp_unary (u : 𝓞 F) : Qp v (QuadForm.diag ![u]) = QuadForm.diag ![ι v u] := by
  rw [Qp_diag]; congr 1; funext i; fin_cases i; rfl

/-- **Squares in $F_\mathfrak p$ and in $\mathfrak o_\mathfrak p$** for a quotient of units: for $u, m \in \mathfrak o_\mathfrak p$ with $u$ a unit,
$m/u \in F_\mathfrak p^{\times 2}$ iff $u y^2 = m$ for some $y \in \mathfrak o_\mathfrak p$. -/
theorem isSquare_div_iff {u m : 𝔬} (hu : IsUnit u) :
    IsSquare ((m : Fv) / (u : Fv)) ↔ ∃ y : 𝔬, u * y ^ 2 = m := by
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have hu0 : (u : Fv) ≠ 0 := by
    intro h; apply hu.ne_zero; exact_mod_cast h
  have hdiv : (m : Fv) / (u : Fv) = algebraMap 𝔬 Fv (m * w) := by
    have hw' : (u : Fv) * (w : Fv) = 1 := by exact_mod_cast congrArg (fun z : 𝔬 => (z : Fv)) hw
    rw [div_eq_iff hu0]
    show (m : Fv) = ((m * w : 𝔬) : Fv) * (u : Fv)
    push_cast
    rw [mul_assoc, mul_comm (w : Fv), hw', mul_one]
  rw [hdiv, DVR.isSquare_algebraMap_iff]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    calc u * y ^ 2 = u * (m * w) := by rw [hy]; ring
      _ = m * (u * w) := by ring
      _ = m := by rw [hw, mul_one]
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [← hy]
    calc u * y ^ 2 * w = y ^ 2 * (u * w) := by ring
      _ = y * y := by rw [hw]; ring

open Classical in
/-- **$\beta_\mathfrak p(u x^2;\, m)$ for units at a dyadic prime of $F$** (any ramification; $e = \mathrm{ord}_\mathfrak p 2$):
$$\beta_\mathfrak p(m) = \begin{cases} 2(N\mathfrak p)^e & m/u \in F_\mathfrak p^{\times 2},\\ 0 & \text{otherwise}\end{cases}
\qquad (u, m \notin \mathfrak p).$$
With `HN.index_sq_U0` ($[\mathfrak o_\mathfrak p^\times : \mathfrak o_\mathfrak p^{\times 2}] = 2(N\mathfrak p)^e$) the average over unit
classes is $1$, as it must be. From `DVR.localDensity_unary_unit_complete`. -/
@[kb "hanke2004" "p. 362 (dyadic case-by-case: n = 1, over F)"]
theorem localDensity_unary_unit (h2 : (2 : 𝓞 F) ∈ v.asIdeal) {u m : 𝓞 F} (hu : u ∉ v.asIdeal)
    (hm : m ∉ v.asIdeal) :
    localDensity v (QuadForm.diag ![u]) m =
      if IsSquare ((ι v m : Fv) / (ι v u : Fv)) then 2 * N𝔭 ^ ordTwo v else 0 := by
  have hu' : ¬ π v ∣ ι v u := by rwa [π_dvd_ι_iff]
  rw [localDensity_eq_completion, Qp_unary, DVR.localDensity_unary_unit_complete _ (irreducible_π v)
    (π_dvd_two v h2) (two_ne_zero' v) _ (ordTwo_spec v) hu' (by rwa [π_dvd_ι_iff]), q_completion,
    isSquare_div_iff v (DVR.dvr_isUnit_of_not_dvd (irreducible_π v) hu')]

open Classical in
/-- **$\beta_\mathfrak p(u x^2;\, m)$ for every $m \ne 0$ at a dyadic prime of $F$**: for $u \notin \mathfrak p$ and
$m \in \mathfrak p^a \setminus \mathfrak p^{a+1}$, $\beta_\mathfrak p(m) = 2(N\mathfrak p)^{e + a/2}$ if $a$ is even and $(m/\varpi^a)/u$ is a square in
$\mathfrak o_\mathfrak p$ (equivalently in $F_\mathfrak p$, `NF.isSquare_div_iff`), else $0$. From `DVR.localDensity_unary_complete`. -/
@[kb "hanke2004" "§3, (5.7), p. 369; p. 362 (dyadic, n = 1, over F)"]
theorem localDensity_unary (h2 : (2 : 𝓞 F) ∈ v.asIdeal) {u : 𝓞 F} (hu : u ∉ v.asIdeal) {a : ℕ} {m : 𝓞 F}
    (hda : m ∈ v.asIdeal ^ a) (ha : m ∉ v.asIdeal ^ (a + 1)) :
    localDensity v (QuadForm.diag ![u]) m =
      if Even a ∧ ∃ y : 𝔬, ι v u * y ^ 2 = DVR.divPow (π v) a (ι v m) then 2 * N𝔭 ^ (ordTwo v + a / 2)
      else 0 := by
  have hu' : ¬ π v ∣ ι v u := by rwa [π_dvd_ι_iff]
  rw [localDensity_eq_completion, Qp_unary, DVR.localDensity_unary_complete _ (irreducible_π v)
    (π_dvd_two v h2) (two_ne_zero' v) _ (ordTwo_spec v) hu' ((π_pow_dvd_ι_iff v a m).2 hda)
    (by rwa [π_pow_dvd_ι_iff]), q_completion]

end QuadFormsKB.LocalDensity.NF
