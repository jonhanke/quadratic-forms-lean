/-
# Local densities over a number field: the headline local results at every $\mathfrak p$

**Layer:** number field (statements for $Q$ = `QuadForm (𝓞 F) n` at a finite prime $\mathfrak p$ = `v`).
**Defines** the local density $\beta_\mathfrak p(Q, m) = \lim_k r_{\mathfrak p^k}(m)/(N\mathfrak p)^{k(n-1)}$ directly over
$\mathcal O_F$ (`NF.localDensity`), the primitive density, the local constant $C_\mathfrak p$, and the notions
"locally represented" / "$\mathfrak p$-stable" over $\mathcal O_F$; each agrees with its DVR counterpart at the
completion $\mathfrak o_\mathfrak p$ (`localDensity_eq_completion`, …). **Proves**, each as a short instantiation
of the DVR theory through `NFBridge.lean`: existence of $\beta_\mathfrak p$ (5.2); the corrected normal form
(Lemma 2.1) and the printed one when $\mathfrak p^2 \nmid 2$; Lemma 3.2; Lemma 3.8 (corrected) and Cor. 3.8.2;
(5.6), (5.7), (5.8), (5.10), (5.11) and $C_\mathfrak p > 0$. The uniformizer is the global integer
$\varpi$ = `unif v` $\in \mathfrak p \setminus \mathfrak p^2$. Isotropy is over the completion $F_\mathfrak p$.
-/
import QuadFormsKB.LocalDensity.NFBridge

open NumberField IsDedekindDomain WithZero Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.LocalDensity.NF

open QuadForm

variable {F : Type*} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "N𝔭" => (Ideal.absNorm v.asIdeal : ℝ)

/-! ### Isotropy over $F_\mathfrak p$ and diagonal forms -/

/-- Evaluating the base change $Q \otimes \mathfrak o_\mathfrak p$ in $F_\mathfrak p$ is evaluating $Q$ in $F_\mathfrak p$. -/
theorem evalIn_Qp (Q : QuadForm (𝓞 F) n) (x : Fin n → Fv) : (Qp v Q).evalIn Fv x = Q.evalIn Fv x := by
  have h : ∀ c : 𝓞 F, algebraMap 𝔬 Fv (ι v c) = algebraMap (𝓞 F) Fv c := fun _ => rfl
  simp only [QuadForm.evalIn, QuadForm.map, Matrix.map_apply, h]

/-- $Q \otimes \mathfrak o_\mathfrak p$ is isotropic over $F_\mathfrak p$ iff $Q$ is. -/
theorem isotropicIn_Qp_iff (Q : QuadForm (𝓞 F) n) : (Qp v Q).IsotropicIn Fv ↔ Q.IsotropicIn Fv := by
  simp only [QuadForm.IsotropicIn, evalIn_Qp]

/-- The base change of a diagonal form is diagonal. -/
theorem Qp_diag (a : Fin n → 𝓞 F) : Qp v (QuadForm.diag a) = QuadForm.diag fun i => ι v (a i) := by
  ext i j
  simp only [QuadForm.map, QuadForm.diag, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

/-- $\varpi \mid \iota(a) \iff a \in \mathfrak p$. -/
theorem π_dvd_ι_iff (a : 𝓞 F) : π v ∣ ι v a ↔ a ∈ v.asIdeal := by
  rw [← pow_one (π v), π_pow_dvd_ι_iff, pow_one]

/-! ### Densities over $\mathcal O_F$ -/

/-- **The local density $\beta_\mathfrak p(Q, m)$** over $\mathcal O_F$ (Hanke 2004, (5.1)–(5.2), p. 368, with the
corrected exponent): $\beta_\mathfrak p(m) = \lim_k r_{\mathfrak p^k}(m)/(N\mathfrak p)^{k(n-1)}$. It equals the DVR density at
the completion (`localDensity_eq_completion`); the limit exists for $Q$ nondegenerate and $m \ne 0$
(`localDensity_eventually_eq`). -/
@[kb "hanke2004" "(5.1)–(5.2), p. 368"]
def localDensity (Q : QuadForm (𝓞 F) n) (m : 𝓞 F) : ℝ :=
  limUnder atTop fun k : ℕ => (repCount v Q k m : ℝ) / N𝔭 ^ (k * (n - 1))

/-- **Primitive (non-Zero-type) local density** over $\mathcal O_F$ (Hanke 2004, Def. 5.1, p. 368):
$\beta^{\mathrm{Good}\cup\mathrm{Bad}}_\mathfrak p(m) = \lim_k r^{\mathrm{Good}\cup\mathrm{Bad}}_{\mathfrak p^k}(m)/(N\mathfrak p)^{k(n-1)}$. -/
def localDensityPrim (Q : QuadForm (𝓞 F) n) (m : 𝓞 F) : ℝ :=
  limUnder atTop fun k : ℕ =>
    (repCountOf v Q k m (fun x => ¬ IsZeroType v k x) : ℝ) / N𝔭 ^ (k * (n - 1))

/-- **The local constant $C_\mathfrak p(T)$** (Hanke 2004, after (5.8), p. 370):
$C_\mathfrak p(T) = \frac{N\mathfrak p^{n-2}}{N\mathfrak p^{n-2} - 1} \cdot \frac{\beta^{\mathrm{Good}\cup\mathrm{Bad}}_\mathfrak p(\varpi^2 T)}{\beta_\mathfrak p(T)}$. -/
@[kb "hanke2004" "after (5.8), p. 370"]
def localConstC (Q : QuadForm (𝓞 F) n) (T : 𝓞 F) : ℝ :=
  (N𝔭 ^ (n - 2) / (N𝔭 ^ (n - 2) - 1)) *
    (localDensityPrim v Q (unif v ^ 2 * T) / localDensity v Q T)

/-- $C'_\mathfrak p(T) = \min(1, C_\mathfrak p(T))$ (Hanke 2004, (5.11), p. 371). -/
def localConstC' (Q : QuadForm (𝓞 F) n) (T : 𝓞 F) : ℝ := min 1 (localConstC v Q T)

/-- **Locally represented at $\mathfrak p$** (Hanke 2004, Def. 3.5, p. 362): $r_{\mathfrak p^k}(m) > 0$ for all
large $k$. -/
def IsLocallyRepresentedAt (Q : QuadForm (𝓞 F) n) (m : 𝓞 F) : Prop :=
  ∀ᶠ k in atTop, 0 < repCount v Q k m

/-- **$\mathfrak p$-stable** (Hanke 2004, Def. 3.6, p. 362): $m$ is locally represented at $\mathfrak p$, and for all
large $k$ the number of non-Zero-type solutions mod $\mathfrak p^k$ of $Q = \varpi^{2\nu} m$ is the same for
every $\nu \ge 1$. -/
@[kb "hanke2004" "Def. 3.6, p. 362"]
def IsPStable (Q : QuadForm (𝓞 F) n) (m : 𝓞 F) : Prop :=
  IsLocallyRepresentedAt v Q m ∧
    ∀ᶠ k in atTop, ∀ ν ≥ 1,
      repCountOf v Q k (unif v ^ (2 * ν) * m) (fun x => ¬ IsZeroType v k x) =
        repCountOf v Q k (unif v ^ 2 * m) (fun x => ¬ IsZeroType v k x)

/-! ### Agreement with the completion -/

theorem localDensity_eq_completion (Q : QuadForm (𝓞 F) n) (m : 𝓞 F) :
    localDensity v Q m = DVR.localDensity (Qp v Q) (π v) (ι v m) := by
  simp only [localDensity, DVR.localDensity, repCount_eq_completion, q_completion]

theorem localDensityPrim_eq_completion (Q : QuadForm (𝓞 F) n) (m : 𝓞 F) :
    localDensityPrim v Q m =
      DVR.localDensityOf (Qp v Q) (π v) (ι v m) (fun k x => ¬ DVR.IsZeroType (π v) k x) := by
  simp only [localDensityPrim, DVR.localDensityOf, repCountNonZero_eq_completion, q_completion]

theorem localConstC_eq_completion (Q : QuadForm (𝓞 F) n) (T : 𝓞 F) :
    localConstC v Q T = DVR.localConstC (Qp v Q) (π v) (ι v T) := by
  simp only [localConstC, DVR.localConstC, localDensityPrim_eq_completion, localDensity_eq_completion,
    q_completion, map_mul, map_pow]

theorem localConstC'_eq_completion (Q : QuadForm (𝓞 F) n) (T : 𝓞 F) :
    localConstC' v Q T = DVR.localConstC' (Qp v Q) (π v) (ι v T) := by
  simp only [localConstC', DVR.localConstC', localConstC_eq_completion]

theorem isLocallyRepresentedAt_iff (Q : QuadForm (𝓞 F) n) (m : 𝓞 F) :
    IsLocallyRepresentedAt v Q m ↔ DVR.IsLocallyRepresentedAt (Qp v Q) (π v) (ι v m) := by
  simp only [IsLocallyRepresentedAt, DVR.IsLocallyRepresentedAt, repCount_eq_completion]

theorem isPStable_iff (Q : QuadForm (𝓞 F) n) (S₀ : Finset (Fin n)) (m : 𝓞 F) :
    IsPStable v Q m ↔ DVR.IsPStable (Qp v Q) S₀ (π v) (ι v m) := by
  simp only [IsPStable, DVR.IsPStable, isLocallyRepresentedAt_iff, repCountNonZero_eq_completion,
    map_mul, map_pow]

/-! ### The headline local results over $F$ -/

/-- **Existence of $\beta_\mathfrak p$ at every prime** (Hanke 2004, (5.2), p. 368): for $Q$ nondegenerate over
$\mathcal O_F$ and $m \ne 0$, the normalized counts $r_{\mathfrak p^k}(m)/(N\mathfrak p)^{k(n-1)}$ are eventually equal to
$\beta_\mathfrak p(Q, m)$, at every finite prime $\mathfrak p$ (dyadic or not). From `DVR.localDensity_eventually_eq`. -/
@[kb "hanke2004" "(5.2), p. 368"]
theorem localDensity_eventually_eq (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (m : 𝓞 F)
    (hm : m ≠ 0) :
    ∀ᶠ k in atTop, (repCount v Q k m : ℝ) / N𝔭 ^ (k * (n - 1)) = localDensity v Q m := by
  have h := DVR.localDensity_eventually_eq (Qp v Q) (nondegenerate_Qp v hQ) (π v) (irreducible_π v)
    (ι v m) (ι_ne_zero v hm) (two_ne_zero' v)
  simpa only [← repCount_eq_completion, q_completion, ← localDensity_eq_completion] using h

/-- **The limit defining $\beta_\mathfrak p(Q, m)$ exists** (Hanke 2004, (5.2), p. 368). -/
@[kb "hanke2004" "(5.2), p. 368"]
theorem tendsto_localDensity (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (m : 𝓞 F) (hm : m ≠ 0) :
    Tendsto (fun k : ℕ => (repCount v Q k m : ℝ) / N𝔭 ^ (k * (n - 1))) atTop
      (𝓝 (localDensity v Q m)) :=
  tendsto_const_nhds.congr' (by
    filter_upwards [localDensity_eventually_eq v Q hQ m hm] with k hk using hk.symm)

/-- **Local normal form over $\mathfrak o_\mathfrak p$, corrected** (Hanke 2004, Lemma 2.1, p. 355, corrected; see
`docs/updates-and-errata.md`): every nondegenerate $Q$ over $\mathcal O_F$ has the counts mod $\mathfrak p^k$ of a form
$Q'$ over $\mathfrak o_\mathfrak p$ in the general normal form `IsJordanFormW`, with no 2-dimensional blocks when
$\mathfrak p \nmid 2$. From `DVR.exists_jordanFormW`. -/
@[kb "hanke2004" "Lemma 2.1, p. 355 (corrected)"]
theorem exists_jordanFormW (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) :
    ∃ (Q' : QuadForm 𝔬 n) (P : Finset (Fin n × Fin n)) (w : Fin n → ℕ),
      DVR.IsJordanFormW Q' (π v) P w ∧ ((2 : 𝓞 F) ∉ v.asIdeal → P = ∅) ∧
        ∀ k m, repCount v Q k m = DVR.repCount Q' (π v) k (ι v m) := by
  obtain ⟨Q', P, w, hJ, hP, hc⟩ :=
    DVR.exists_jordanFormW (Qp v Q) (nondegenerate_Qp v hQ) (π v) (irreducible_π v) (two_ne_zero' v)
  refine ⟨Q', P, w, hJ, fun h2 => hP ?_, fun k m => by rw [repCount_eq_completion, hc]⟩
  rwa [← pow_one (π v), π_pow_dvd_two_iff, pow_one]

/-- **Local normal form as printed, when $\mathfrak p^2 \nmid 2$** (Hanke 2004, Lemma 2.1, p. 355): then the printed
normal form `DVR.IsJordanForm` exists over $\mathfrak o_\mathfrak p$, with the counts of $Q$. From
`DVR.exists_jordanForm`. -/
@[kb "hanke2004" "Lemma 2.1, p. 355"]
theorem exists_jordanForm (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate)
    (h2 : (2 : 𝓞 F) ∉ v.asIdeal ^ 2) :
    ∃ (Q' : QuadForm 𝔬 n) (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ),
      DVR.IsJordanForm Q' (π v) P ν ∧ ((2 : 𝓞 F) ∉ v.asIdeal → P = ∅) ∧
        ∀ k m, repCount v Q k m = DVR.repCount Q' (π v) k (ι v m) := by
  obtain ⟨Q', P, ν, hJ, hP, hc⟩ := DVR.exists_jordanForm (Qp v Q) (nondegenerate_Qp v hQ) (π v)
    (irreducible_π v) (by rwa [π_pow_dvd_two_iff])
  refine ⟨Q', P, ν, hJ, fun h2 => hP ?_, fun k m => by rw [repCount_eq_completion, hc]⟩
  rwa [← pow_one (π v), π_pow_dvd_two_iff, pow_one]

/-- **The printed and the corrected normal forms agree when $\mathfrak p^2 \nmid 2$** (Hanke 2004, Lemma 2.1,
p. 355). From `DVR.isJordanForm_iff_isJordanFormW`. -/
@[kb "hanke2004" "Lemma 2.1, p. 355"]
theorem isJordanForm_iff_isJordanFormW (h2 : (2 : 𝓞 F) ∉ v.asIdeal ^ 2) {Q' : QuadForm 𝔬 n}
    {P : Finset (Fin n × Fin n)} {ν : Fin n → ℕ} :
    DVR.IsJordanForm Q' (π v) P ν ↔ DVR.IsJordanFormW Q' (π v) P ν :=
  DVR.isJordanForm_iff_isJordanFormW (irreducible_π v) (by rwa [π_pow_dvd_two_iff])

/-- **Lemma 3.2 over $F$** (Hanke 2004, Lemma 3.2, eq. (3.1), p. 358): if $Q \otimes \mathfrak o_\mathfrak p$ is in normal
form with gradient bound $t$, then for $k \ge 2t + 1$ and $l \ge 0$,
$r^{\mathrm{Good}}_{\mathfrak p^{k+l}}(m) = (N\mathfrak p)^{(n-1)l}\, r^{\mathrm{Good}}_{\mathfrak p^k}(m)$ (Good type relative to the
unimodular coordinates). From `DVR.repCountGood_add_of_gradBound`. -/
@[kb "hanke2004" "Lemma 3.2, eq. (3.1), p. 358"]
theorem repCountGood_add_of_gradBound (Q : QuadForm (𝓞 F) n) (P : Finset (Fin n × Fin n))
    (w : Fin n → ℕ) (hJ : DVR.IsJordanFormW (Qp v Q) (π v) P w) (t : ℕ)
    (hB : DVR.GradBound (Qp v Q) (π v) P w t) (m : 𝓞 F) (k l : ℕ) (hk : 2 * t + 1 ≤ k) :
    repCountOf v Q (k + l) m (IsGoodType v (unimodularCoords w) (k + l)) =
      Ideal.absNorm v.asIdeal ^ ((n - 1) * l) *
        repCountOf v Q k m (IsGoodType v (unimodularCoords w) k) := by
  rw [repCountGood_eq_completion, repCountGood_eq_completion,
    DVR.repCountGood_add_of_gradBound _ _ (irreducible_π v) P w hJ t hB _ k l hk, q_completion]

/-- **Lemma 3.2 over $F$ with $t = \mathrm{ord}_\mathfrak p(2)$** (Hanke 2004, Lemma 3.2, eq. (3.1), p. 358): for
$Q \otimes \mathfrak o_\mathfrak p$ in normal form, $2 \in \mathfrak p^e \setminus \mathfrak p^{e+1}$, $k \ge 2e + 1$:
$r^{\mathrm{Good}}_{\mathfrak p^{k+l}}(m) = (N\mathfrak p)^{(n-1)l}\, r^{\mathrm{Good}}_{\mathfrak p^k}(m)$. From
`DVR.repCountGood_add`. -/
@[kb "hanke2004" "Lemma 3.2, eq. (3.1), p. 358"]
theorem repCountGood_add (Q : QuadForm (𝓞 F) n) (P : Finset (Fin n × Fin n)) (w : Fin n → ℕ)
    (hJ : DVR.IsJordanFormW (Qp v Q) (π v) P w) (e : ℕ)
    (he : (2 : 𝓞 F) ∈ v.asIdeal ^ e ∧ (2 : 𝓞 F) ∉ v.asIdeal ^ (e + 1)) (m : 𝓞 F) (k l : ℕ)
    (hk : 2 * e + 1 ≤ k) :
    repCountOf v Q (k + l) m (IsGoodType v (unimodularCoords w) (k + l)) =
      Ideal.absNorm v.asIdeal ^ ((n - 1) * l) *
        repCountOf v Q k m (IsGoodType v (unimodularCoords w) k) := by
  rw [repCountGood_eq_completion, repCountGood_eq_completion,
    DVR.repCountGood_add _ _ (irreducible_π v) P w hJ e
      ⟨(π_pow_dvd_two_iff v e).mpr he.1, fun h => he.2 ((π_pow_dvd_two_iff v _).mp h)⟩ _ k l hk,
    q_completion]

/-- **Lemma 3.8 over $F$, corrected** (Hanke 2004, Lemma 3.8, p. 363, corrected): for $m$ $\mathfrak p$-stable,
$Q$ is anisotropic over $F_\mathfrak p$ iff eventually every solution of $Q \equiv \varpi^2 m \pmod{\mathfrak p^k}$ is of
Zero type. From `DVR.anisotropic_iff_zeroType` (which needs `isAdicComplete`). -/
@[kb "hanke2004" "Lemma 3.8, p. 363 (corrected)"]
theorem anisotropic_iff_zeroType (Q : QuadForm (𝓞 F) n) (m : 𝓞 F) (hm : IsPStable v Q m) :
    ¬ Q.IsotropicIn Fv ↔
      ∀ᶠ k in atTop,
        repCount v Q k (unif v ^ 2 * m) = repCountOf v Q k (unif v ^ 2 * m) (IsZeroType v k) := by
  have h := DVR.anisotropic_iff_zeroType Fv (Qp v Q) (π v) (irreducible_π v) ∅ (ι v m)
    ((isPStable_iff v Q ∅ m).mp hm)
  rw [isotropicIn_Qp_iff] at h
  simpa only [repCount_eq_completion, repCountZero_eq_completion, map_mul, map_pow] using h

/-- **Cor. 3.8.2 over $F$, for a principal prime** (Hanke 2004, Cor. 3.8.2, p. 364): if $\mathfrak p = (p)$ is
principal, $Q$ is anisotropic over $F_\mathfrak p$ and $m$ is $p$-stable (at the completion), then $Q$ has as
many global solutions $\vec x \in \mathcal O_F^n$ of $Q(\vec x) = p^{2e} m$ as of $Q(\vec x) = m$.
*Hypothesis:* the principality of $\mathfrak p$ is what lets the global equation see $p$; the DVR
statement asks for $A \ni p$ with $\pi \mid \varphi(a) \Rightarrow p \mid a$. From `DVR.card_rep_mul_pow_sq`. -/
@[kb "hanke2004" "Cor. 3.8.2, p. 364"]
theorem card_rep_mul_pow_sq (p : 𝓞 F) (hp : v.asIdeal = Ideal.span {p}) (Q : QuadForm (𝓞 F) n)
    (S₀ : Finset (Fin n)) (haniso : ¬ Q.IsotropicIn Fv) (m : 𝓞 F)
    (hm : DVR.IsPStable (Qp v Q) S₀ (ι v p) (ι v m)) (e : ℕ) :
    Set.ncard {x : Fin n → 𝓞 F | Q.eval x = p ^ (2 * e) * m} =
      Set.ncard {x : Fin n → 𝓞 F | Q.eval x = m} := by
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
  have hA : ∀ a : 𝓞 F, ι v p ∣ ι v a → p ∣ a := by
    intro a ha
    have hass : Associated (π v) (ι v p) :=
      IsDiscreteValuationRing.associated_of_irreducible _ (irreducible_π v) hirr
    rw [← Ideal.mem_span_singleton, ← hp, ← π_dvd_ι_iff]
    exact hass.dvd.trans ha
  have h := DVR.card_rep_mul_pow_sq Fv (ι v) Q p (ι v p) hirr rfl hA S₀
    (by rwa [← Qp, isotropicIn_Qp_iff]) m hm e
  exact h

/-- **(5.6) over $F$** (Hanke 2004, (5.6), p. 369): for $n \ge 3$, $Q$ nondegenerate, $m \ne 0$:
$\beta_\mathfrak p(m) \le (N\mathfrak p)^{n-2}\, \beta_\mathfrak p(\varpi^2 m)$. From `DVR.localDensity_le_mul_sq`. -/
@[kb "hanke2004" "(5.6), p. 369"]
theorem localDensity_le_mul_sq (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n)
    (m : 𝓞 F) (hm : m ≠ 0) :
    localDensity v Q m ≤ N𝔭 ^ (n - 2) * localDensity v Q (unif v ^ 2 * m) := by
  have h := DVR.localDensity_le_mul_sq (Qp v Q) (nondegenerate_Qp v hQ) hn (π v) (irreducible_π v)
    (two_ne_zero' v) (ι v m) (ι_ne_zero v hm)
  simpa only [localDensity_eq_completion, q_completion, map_mul, map_pow] using h

/-- **(5.7) over $F$** (Hanke 2004, (5.7), p. 369): for $Q$ nondegenerate and isotropic over $F_\mathfrak p$ and
$T \ne 0$ $\mathfrak p$-stable,
$\beta_\mathfrak p(\varpi^{2e} T) = \beta^{\mathrm{Good}\cup\mathrm{Bad}}_\mathfrak p(\varpi^2 T) \sum_{i<e} (N\mathfrak p^{n-2})^{-i} +
\beta_\mathfrak p(T)/(N\mathfrak p)^{(n-2)e}$. From `DVR.localDensity_pow_sq`. -/
@[kb "hanke2004" "(5.7), p. 369"]
theorem localDensity_pow_sq (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hiso : Q.IsotropicIn Fv)
    (T : 𝓞 F) (hT0 : T ≠ 0) (hT : IsPStable v Q T) (e : ℕ) :
    localDensity v Q (unif v ^ (2 * e) * T) =
      localDensityPrim v Q (unif v ^ 2 * T) * ∑ i ∈ Finset.range e, (N𝔭 ^ (n - 2))⁻¹ ^ i +
        localDensity v Q T / N𝔭 ^ ((n - 2) * e) := by
  have h := DVR.localDensity_pow_sq Fv (Qp v Q) (nondegenerate_Qp v hQ) (π v) (irreducible_π v)
    (two_ne_zero' v) ∅ ((isotropicIn_Qp_iff v Q).mpr hiso) (ι v T) (ι_ne_zero v hT0)
    ((isPStable_iff v Q ∅ T).mp hT) e
  simpa only [localDensity_eq_completion, localDensityPrim_eq_completion, q_completion, map_mul,
    map_pow] using h

/-- **(5.8) over $F$** (Hanke 2004, (5.8), p. 369): for $n \ge 3$, $Q$ nondegenerate, $T \ne 0$ $\mathfrak p$-stable:
$\beta_\mathfrak p(\varpi^{2\nu} T)/\beta_\mathfrak p(T) = C_\mathfrak p(T) + (1 - C_\mathfrak p(T))/(N\mathfrak p)^{(n-2)\nu}$. From
`DVR.localDensity_pow_sq_div`. -/
@[kb "hanke2004" "(5.8), p. 369"]
theorem localDensity_pow_sq_div (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n)
    (T : 𝓞 F) (hT0 : T ≠ 0) (hT : IsPStable v Q T) (ν : ℕ) :
    localDensity v Q (unif v ^ (2 * ν) * T) / localDensity v Q T =
      localConstC v Q T + (1 - localConstC v Q T) / N𝔭 ^ ((n - 2) * ν) := by
  have h := DVR.localDensity_pow_sq_div (Qp v Q) (nondegenerate_Qp v hQ) hn (π v) (irreducible_π v)
    (two_ne_zero' v) ∅ (ι v T) (ι_ne_zero v hT0) ((isPStable_iff v Q ∅ T).mp hT) ν
  simpa only [localDensity_eq_completion, localConstC_eq_completion, q_completion, map_mul,
    map_pow] using h

/-- **$C_\mathfrak p > 0$ for isotropic $Q$** (Hanke 2004, proof of Thm 5.4, p. 370): for $n \ge 3$, $Q$
nondegenerate and isotropic over $F_\mathfrak p$, $T \ne 0$ $\mathfrak p$-stable, $C_\mathfrak p(T) > 0$. From
`DVR.localConstC_pos` (which needs `isAdicComplete`). -/
@[kb "hanke2004" "Proof of Thm 5.4, p. 370 (C_p > 0)"]
theorem localConstC_pos (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n)
    (hiso : Q.IsotropicIn Fv) (T : 𝓞 F) (hT0 : T ≠ 0) (hT : IsPStable v Q T) :
    0 < localConstC v Q T := by
  rw [localConstC_eq_completion]
  exact DVR.localConstC_pos Fv (Qp v Q) (nondegenerate_Qp v hQ) hn (π v) (irreducible_π v)
    (two_ne_zero' v) ∅ ((isotropicIn_Qp_iff v Q).mpr hiso) (ι v T) (ι_ne_zero v hT0)
    ((isPStable_iff v Q ∅ T).mp hT)

/-- **(5.11) over $F$** (Hanke 2004, (5.11), p. 371): for $n \ge 3$, $Q$ nondegenerate, $T \ne 0$
$\mathfrak p$-stable: $C'_\mathfrak p(T)\, \beta_\mathfrak p(T) \le \beta_\mathfrak p(\varpi^{2\nu} T)$. From
`DVR.localDensity_pow_sq_ge`. -/
@[kb "hanke2004" "(5.11), p. 371"]
theorem localDensity_pow_sq_ge (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n)
    (T : 𝓞 F) (hT0 : T ≠ 0) (hT : IsPStable v Q T) (ν : ℕ) :
    localConstC' v Q T * localDensity v Q T ≤ localDensity v Q (unif v ^ (2 * ν) * T) := by
  have h := DVR.localDensity_pow_sq_ge (Qp v Q) (nondegenerate_Qp v hQ) hn (π v) (irreducible_π v)
    (two_ne_zero' v) ∅ (ι v T) (ι_ne_zero v hT0) ((isPStable_iff v Q ∅ T).mp hT) ν
  simpa only [localDensity_eq_completion, localConstC'_eq_completion, map_mul, map_pow] using h

/-- **(5.11) over $F$, ratio form** (Hanke 2004, (5.11), p. 371):
$C'_\mathfrak p(T) \le \beta_\mathfrak p(\varpi^{2\nu} T)/\beta_\mathfrak p(T)$. From `DVR.localDensity_pow_sq_div_ge`. -/
@[kb "hanke2004" "(5.11), p. 371"]
theorem localDensity_pow_sq_div_ge (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 3 ≤ n)
    (T : 𝓞 F) (hT0 : T ≠ 0) (hT : IsPStable v Q T) (ν : ℕ) :
    localConstC' v Q T ≤ localDensity v Q (unif v ^ (2 * ν) * T) / localDensity v Q T := by
  have h := DVR.localDensity_pow_sq_div_ge (Qp v Q) (nondegenerate_Qp v hQ) hn (π v)
    (irreducible_π v) (two_ne_zero' v) ∅ (ι v T) (ι_ne_zero v hT0) ((isPStable_iff v Q ∅ T).mp hT) ν
  simpa only [localDensity_eq_completion, localConstC'_eq_completion, map_mul, map_pow] using h

/-- **(5.10) over $F$** (Hanke 2004, (5.10), p. 371): for a ternary diagonal form $\langle a_0, a_1, a_2\rangle$
over $\mathcal O_F$ with unit coefficients at a non-dyadic $\mathfrak p$, the factor
$C_\mathfrak p + (1 - C_\mathfrak p)/(N\mathfrak p)^\nu$ is $1$ if $T \notin \mathfrak p$ and $-a_0a_1a_2T$ is a square mod $\mathfrak p$;
$(N\mathfrak p^\nu + 2\sum_{\mu<\nu} N\mathfrak p^\mu)/N\mathfrak p^\nu$ if it is a non-square; and
$\sum_{\mu \le \nu} N\mathfrak p^\mu / N\mathfrak p^\nu$ if $T \in \mathfrak p \setminus \mathfrak p^2$. The quadratic character is that of
the residue field of $\mathfrak o_\mathfrak p$. From `DVR.eq_5_10`. -/
@[kb "hanke2004" "(5.10), p. 371"]
theorem eq_5_10 (a : Fin 3 → 𝓞 F) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (ha : ∀ i, a i ∉ v.asIdeal)
    (T : 𝓞 F) (ν : ℕ) :
    let C := localConstC v (QuadForm.diag a) T
    let ψ := quadraticChar (IsLocalRing.ResidueField 𝔬)
      (IsLocalRing.residue 𝔬 (ι v (-(∏ i, a i) * T)))
    (T ∉ v.asIdeal → ψ = 1 → C + (1 - C) / N𝔭 ^ ν = 1) ∧
    (T ∉ v.asIdeal → ψ = -1 →
      C + (1 - C) / N𝔭 ^ ν = (N𝔭 ^ ν + 2 * ∑ μ ∈ Finset.range ν, N𝔭 ^ μ) / N𝔭 ^ ν) ∧
    (T ∈ v.asIdeal → T ∉ v.asIdeal ^ 2 →
      C + (1 - C) / N𝔭 ^ ν = (∑ μ ∈ Finset.range (ν + 1), N𝔭 ^ μ) / N𝔭 ^ ν) := by
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

/-! ### Consistency with the rational theory ($F = \mathbb Q$) -/

section Rat

variable (w : HeightOneSpectrum (𝓞 ℚ))

/-- $\mathcal O_\mathbb Q/\mathfrak p^k \cong \mathbb Z/p^k$ for $\mathfrak p = (p)$, $p$ = `natGenerator w`. -/
def ratQuotEquiv (k : ℕ) :
    𝓞 ℚ ⧸ w.asIdeal ^ k ≃+* ZMod (Rat.HeightOneSpectrum.natGenerator w ^ k) :=
  (Ideal.quotientEquiv _ _ (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) rfl).trans
    ((Ideal.quotEquivOfEq (by
      rw [Ideal.map_pow]
      erw [← Rat.HeightOneSpectrum.span_natGenerator]
      rw [Ideal.span_singleton_pow]
      push_cast; rfl)).trans
      (Int.quotientSpanNatEquivZMod (Rat.HeightOneSpectrum.natGenerator w ^ k)))

/-- **Counts over $\mathcal O_\mathbb Q$ are the rational counts:** for an integral form $Q$ and the prime $p$
under $\mathfrak p$, $r_{\mathfrak p^k}(Q, m) = r_{p^k}(Q, m)$. -/
theorem repCount_rat (Q : QuadForm ℤ n) (k : ℕ) (m : ℤ) :
    repCount w (Q.map (Int.castRingHom (𝓞 ℚ))) k (m : 𝓞 ℚ) =
      LocalDensity.repCount Q (Rat.HeightOneSpectrum.natGenerator w) k m := by
  set g := ratQuotEquiv w k
  let E := Equiv.piCongrRight fun _ : Fin n => g.toEquiv
  refine Nat.card_congr (E.subtypeEquiv fun x => ?_)
  rw [evalIn_map_intCast, ← g.injective.eq_iff, map_intCast,
    show g (Q.evalIn _ x) = Q.evalIn _ (E x) from evalIn_intForm_map g.toRingHom Q x, map_intCast]

/-- $N\mathfrak p = p$ for a prime $\mathfrak p$ of $\mathcal O_\mathbb Q$. -/
theorem absNorm_rat : Ideal.absNorm w.asIdeal = Rat.HeightOneSpectrum.natGenerator w := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← pow_one w.asIdeal,
    Nat.card_congr (ratQuotEquiv w 1).toEquiv, Nat.card_zmod, pow_one]

/-- **Consistency check over $\mathbb Q$:** the number-field local density at a prime $\mathfrak p$ of
$\mathcal O_\mathbb Q$ is the rational local density at $p$ (`LocalDensity.localDensity`), for every integral form
$Q$ and $m \in \mathbb Z$. -/
@[kb "hanke2004" "(5.1)–(5.2), p. 368"]
theorem localDensity_rat (Q : QuadForm ℤ n) (m : ℤ) :
    localDensity w (Q.map (Int.castRingHom (𝓞 ℚ))) (m : 𝓞 ℚ) =
      LocalDensity.localDensity Q (Rat.HeightOneSpectrum.natGenerator w) m := by
  simp only [localDensity, LocalDensity.localDensity, repCount_rat, absNorm_rat]

end Rat

end QuadFormsKB.LocalDensity.NF
