/-
# Local densities over a number field: general forms at every prime $\mathfrak p \nmid N$
**Layer:** number field ($Q$ = `QuadForm (𝓞 F) n` at a finite prime $\mathfrak p$ = `v`, uniformizer $\varpi$ = `unif v`).
**Defines** "$\mathfrak p \nmid N$" (`NF.NotDvdLevel v Q`: $\varpi^0$ is a local level of $Q \otimes \mathfrak o_\mathfrak p$, i.e. $H^{-1}$ is integral
at $\mathfrak p$ with diagonal in $2\mathfrak o_\mathfrak p$; Hanke 2004, p. 355). **Proves**, for a general nondegenerate form, at
every prime $\mathfrak p \nmid N$, non-dyadic and dyadic, each a short instantiation of `DVRUnimodular.lean` and
`DVRLevel.lean` through `NFBridge.lean`: Lemma 2.2 at $\mathfrak p \nmid 2$ ($\mathfrak p \nmid N \iff \det H \notin \mathfrak p$); Table 1;
Table 2; (5.12); Remark 3.5.1; the per-place lower bounds L10; and Remark 3.8.1 (isotropy over $F_\mathfrak p$).
$\Phi_n(\mathfrak p)$ is intrinsic: at $\mathfrak p \nmid 2$ the quadratic character of the residue field at $(-1)^{\lfloor n/2\rfloor}D$
($\cdot T'$ for odd $n$; `DVR.chiDisc`, `DVR.chiDiscT`, `DVR.phi` of $Q \otimes \mathfrak o_\mathfrak p$, $D = \det H/2^n$); at $\mathfrak p \mid 2$
the Arf sign $\varepsilon$ (`DVR.arfSignQ`). The residue field is that of $\mathfrak o_\mathfrak p$ ($\cong \mathcal O_F/\mathfrak p$).
-/
import QuadFormsKB.LocalDensity.NFLocal
import QuadFormsKB.LocalDensity.DVRLevel

open NumberField IsDedekindDomain Filter

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.LocalDensity.NF

open QuadForm

variable {F : Type*} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "N𝔭" => (Ideal.absNorm v.asIdeal : ℝ)
local notation "𝔽v" => IsLocalRing.ResidueField 𝔬

/-- **$\mathfrak p \nmid N$** (Hanke 2004, p. 355, the level $N_Q$ at $\mathfrak p$): $Q \otimes \mathfrak o_\mathfrak p$ has $\varpi^0 = 1$ as a local level,
i.e. there is a symmetric $W$ over $\mathfrak o_\mathfrak p$ with even diagonal and $HW = I$ (`DVR.IsLocalLevel`). -/
@[kb "hanke2004" "p. 355 (p ∤ N_Q)"]
def NotDvdLevel (Q : QuadForm (𝓞 F) n) : Prop := DVR.IsLocalLevel (Qp v Q) (π v) 0

theorem det_hessian_Qp (Q : QuadForm (𝓞 F) n) : (Qp v Q).hessian.det = ι v Q.hessian.det := by
  have h : (Qp v Q).hessian = Q.hessian.map (ι v) := by
    ext i j; simp [QuadForm.hessian, QuadForm.map]
  rw [h, ← RingHom.mapMatrix_apply, ← RingHom.map_det]

theorem π_not_dvd_two (h2 : (2 : 𝓞 F) ∉ v.asIdeal) : ¬ π v ∣ 2 := by
  rwa [← map_ofNat (ι v), π_dvd_ι_iff]

theorem π_dvd_two (h2 : (2 : 𝓞 F) ∈ v.asIdeal) : π v ∣ 2 := by
  rwa [← map_ofNat (ι v), π_dvd_ι_iff]

theorem π_not_dvd_det (Q : QuadForm (𝓞 F) n) (hdet : Q.hessian.det ∉ v.asIdeal) :
    ¬ π v ∣ (Qp v Q).hessian.det := by
  rwa [det_hessian_Qp, π_dvd_ι_iff]

/-- **Lemma 2.2 over $F$ at $\mathfrak p \nmid 2$** (Hanke 2004, p. 356): $\mathfrak p \nmid N \iff \mathfrak p \nmid D_{2Q} = \det H$. From
`DVR.isLocalLevel_zero_iff`. -/
@[kb "hanke2004" "Lemma 2.2, p. 356 (p ∤ 2, over F)"]
theorem notDvdLevel_iff (Q : QuadForm (𝓞 F) n) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) :
    NotDvdLevel v Q ↔ Q.hessian.det ∉ v.asIdeal := by
  rw [NotDvdLevel, DVR.isLocalLevel_zero_iff (irreducible_π v) (π_not_dvd_two v h2), det_hessian_Qp,
    π_dvd_ι_iff]

/-! ### Non-dyadic $\mathfrak p \nmid N$ -/

section NonDyadic

variable (Q : QuadForm (𝓞 F) n) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (hN : NotDvdLevel v Q)
include h2 hN

theorem π_not_dvd_det_of_notDvdLevel : ¬ π v ∣ (Qp v Q).hessian.det :=
  π_not_dvd_det v Q ((notDvdLevel_iff v Q h2).1 hN)

/-- **Table 1 over $F$ for a general form** at $\mathfrak p \nmid 2N$ (Hanke 2004, Table 1, p. 363, all $n \ge 1$): with
$\chi_D$ = `DVR.chiDisc (Qp v Q)` $= \chi((-1)^{n/2}D)$, for $u \notin \mathfrak p$: $n$ even: $r_\mathfrak p(0) = N\mathfrak p^{n-1} +
\chi_D(N\mathfrak p - 1)N\mathfrak p^{n/2-1}$, $r_\mathfrak p(u) = N\mathfrak p^{n-1} - \chi_D N\mathfrak p^{n/2-1}$; $n$ odd: $r_\mathfrak p(0) = N\mathfrak p^{n-1}$,
$r_\mathfrak p(u) = N\mathfrak p^{n-1} + \chi((-1)^{(n-1)/2}Du)N\mathfrak p^{(n-1)/2}$. From `DVR.card_mod_pi_of_unimodular`. -/
@[kb "hanke2004" "Table 1, p. 363 (over F, general Q, p ∤ 2N)"]
theorem card_mod_p_of_unimodular (hn : 1 ≤ n) (u : 𝓞 F) (hu : u ∉ v.asIdeal) :
    (Even n →
      (repCount v Q 1 0 : ℤ) = (Ideal.absNorm v.asIdeal : ℤ) ^ (n - 1) + DVR.chiDisc (Qp v Q) *
        ((Ideal.absNorm v.asIdeal : ℤ) - 1) * (Ideal.absNorm v.asIdeal : ℤ) ^ (n / 2 - 1) ∧
      (repCount v Q 1 u : ℤ) = (Ideal.absNorm v.asIdeal : ℤ) ^ (n - 1) -
        DVR.chiDisc (Qp v Q) * (Ideal.absNorm v.asIdeal : ℤ) ^ (n / 2 - 1)) ∧
    (Odd n →
      repCount v Q 1 0 = Ideal.absNorm v.asIdeal ^ (n - 1) ∧
      (repCount v Q 1 u : ℤ) = (Ideal.absNorm v.asIdeal : ℤ) ^ (n - 1) +
        DVR.chiDiscT (Qp v Q) (ι v u) * (Ideal.absNorm v.asIdeal : ℤ) ^ ((n - 1) / 2)) := by
  have h := DVR.card_mod_pi_of_unimodular (Qp v Q) (π v) (irreducible_π v) (π_not_dvd_two v h2)
    (π_not_dvd_det_of_notDvdLevel v Q h2 hN) hn (ι v u) (by rwa [π_dvd_ι_iff])
  simpa only [repCount_eq_completion, map_zero, q_completion] using h

/-- **Remark 3.5.1 over $F$ for a general form** (Hanke 2004, p. 362): for $n \ge 3$ and $\mathfrak p \nmid 2N$, every $m$ is
locally represented at $\mathfrak p$. -/
@[kb "hanke2004" "Remark 3.5.1, p. 362 (over F, general Q)"]
theorem isLocallyRepresentedAt_of_unimodular (hn : 3 ≤ n) (m : 𝓞 F) : IsLocallyRepresentedAt v Q m := by
  rw [isLocallyRepresentedAt_iff]
  exact DVR.isLocallyRepresentedAt_of_unimodular (Qp v Q) hn (π v) (irreducible_π v) (π_not_dvd_two v h2)
    (π_not_dvd_det_of_notDvdLevel v Q h2 hN) (ι v m)

/-- **Table 2 over $F$, $n$ odd, $T' \notin \mathfrak p$** (Hanke 2004, Table 2, p. 370, general $Q$, $\mathfrak p \nmid 2N$):
$C_\mathfrak p(T') = \dfrac{N\mathfrak p^{n-2} - N\mathfrak p^{(n-3)/2}\Phi_n}{N\mathfrak p^{n-2} - 1}$, $\Phi_n = \chi((-1)^{(n-1)/2}DT')$. -/
@[kb "hanke2004" "Table 2, p. 370 (over F, general Q, p ∤ 2N)"]
theorem table2_odd_unit_of_unimodular (hn : 3 ≤ n) (hodd : Odd n) (T : 𝓞 F) (hT : T ∉ v.asIdeal) :
    localConstC v Q T =
      (N𝔭 ^ (n - 2) - N𝔭 ^ ((n - 3) / 2) * DVR.chiDiscT (Qp v Q) (ι v T)) / (N𝔭 ^ (n - 2) - 1) := by
  rw [localConstC_eq_completion, DVR.table2_odd_unit_of_unimodular (Qp v Q) (π v) (irreducible_π v)
    (π_not_dvd_two v h2) (π_not_dvd_det_of_notDvdLevel v Q h2 hN) hn hodd (ι v T) (by rwa [π_dvd_ι_iff]),
    q_completion]

/-- **Table 2 over $F$, $n$ even, $T' \notin \mathfrak p$** (general $Q$, $\mathfrak p \nmid 2N$):
$C_\mathfrak p(T') = \dfrac{N\mathfrak p^{(n-2)/2}}{N\mathfrak p^{(n-2)/2} - \Phi_n}$, $\Phi_n = \chi((-1)^{n/2}D)$. -/
@[kb "hanke2004" "Table 2, p. 370 (over F, general Q, p ∤ 2N)"]
theorem table2_even_unit_of_unimodular (hn : 3 ≤ n) (heven : Even n) (T : 𝓞 F) (hT : T ∉ v.asIdeal) :
    localConstC v Q T = N𝔭 ^ ((n - 2) / 2) / (N𝔭 ^ ((n - 2) / 2) - DVR.chiDisc (Qp v Q)) := by
  rw [localConstC_eq_completion, DVR.table2_even_unit_of_unimodular (Qp v Q) (π v) (irreducible_π v)
    (π_not_dvd_two v h2) (π_not_dvd_det_of_notDvdLevel v Q h2 hN) hn heven (ι v T) (by rwa [π_dvd_ι_iff]),
    q_completion]

/-- **Table 2 over $F$, $T' \in \mathfrak p \setminus \mathfrak p^2$** (general $Q$, $\mathfrak p \nmid 2N$; (5.9)):
$C_\mathfrak p(T') = \dfrac{N\mathfrak p^{n-2}}{N\mathfrak p^{n-2} - 1}$. -/
@[kb "hanke2004" "Table 2, p. 370; (5.9) (over F, general Q, p ∤ 2N)"]
theorem table2_ord_one_of_unimodular (hn : 3 ≤ n) (T : 𝓞 F) (hT1 : T ∈ v.asIdeal) (hT2 : T ∉ v.asIdeal ^ 2) :
    localConstC v Q T = N𝔭 ^ (n - 2) / (N𝔭 ^ (n - 2) - 1) := by
  rw [localConstC_eq_completion, DVR.table2_ord_one_of_unimodular (Qp v Q) (π v) (irreducible_π v)
    (π_not_dvd_two v h2) (π_not_dvd_det_of_notDvdLevel v Q h2 hN) hn (ι v T) (by rwa [π_dvd_ι_iff])
    (by rwa [π_pow_dvd_ι_iff]), q_completion]

/-- **(5.12), corrected, over $F$ for a general form** at non-dyadic $\mathfrak p \nmid N$ (Hanke 2004, p. 371): for
$T' \notin \mathfrak p^2$, $C'_\mathfrak p(T') = 1 \iff n = 3$ or $T' \in \mathfrak p$ or $\Phi_n(\mathfrak p) = (-1)^n$, with the intrinsic
$\Phi_n$ (`DVR.phi`). -/
@[kb "hanke2004" "(5.12), p. 371 (corrected; over F, general Q)"]
theorem eq_5_12_of_unimodular (hn : 3 ≤ n) (T : 𝓞 F) (hT2 : T ∉ v.asIdeal ^ 2) :
    localConstC' v Q T = 1 ↔ n = 3 ∨ T ∈ v.asIdeal ∨ DVR.phi (Qp v Q) (ι v T) = (-1) ^ n := by
  rw [localConstC'_eq_completion, DVR.eq_5_12_of_unimodular (Qp v Q) (π v) (irreducible_π v)
    (π_not_dvd_two v h2) (π_not_dvd_det_of_notDvdLevel v Q h2 hN) hn (ι v T) (by rwa [π_pow_dvd_ι_iff]),
    π_dvd_ι_iff]

open Classical in
/-- **Per-place lower bound L10 over $F$, $n$ even, non-dyadic $\mathfrak p \nmid N$** (proof of Thm 5.7(b),(c), p. 374):
for $m \ne 0$, $\beta_\mathfrak p(m) \ge (1 - \chi_D N\mathfrak p^{-n/2})\frac{X-1}{X+1}$ if $\chi_D = -1$ and $m \in \mathfrak p$, and
$\ge 1 - \chi_D N\mathfrak p^{-n/2}$ otherwise ($X = N\mathfrak p^{(n-2)/2}$). -/
@[kb "hanke2004" "Proof of Thm 5.7(b),(c), p. 374 (over F, p ∤ 2N, n even, general Q)"]
theorem localDensity_ge_even_of_unimodular (hn : 4 ≤ n) (heven : Even n) (m : 𝓞 F) (hm : m ≠ 0) :
    (1 - (DVR.chiDisc (Qp v Q) : ℝ) / N𝔭 ^ (n / 2)) *
        (if DVR.chiDisc (Qp v Q) = -1 ∧ m ∈ v.asIdeal then
          (N𝔭 ^ ((n - 2) / 2) - 1) / (N𝔭 ^ ((n - 2) / 2) + 1) else 1) ≤
      localDensity v Q m := by
  have h := DVR.localDensity_ge_even_of_unimodular (Qp v Q) (π v) (irreducible_π v) (π_not_dvd_two v h2)
    (π_not_dvd_det_of_notDvdLevel v Q h2 hN) hn heven (ι v m) (ι_ne_zero v hm)
  simp only [q_completion, π_dvd_ι_iff, ← localDensity_eq_completion] at h
  convert h using 2

open Classical in
/-- **Per-place lower bound L10 over $F$, $n$ odd, non-dyadic $\mathfrak p \nmid N$** (proof of Thm 5.7(a),(c), p. 375), with
$\Phi = \chi((-1)^{(n-1)/2}DT')$. -/
@[kb "hanke2004" "Proof of Thm 5.7(a),(c), p. 375 (over F, p ∤ 2N, n odd, general Q)"]
theorem localDensity_ge_odd_of_unimodular (hn : 3 ≤ n) (hodd : Odd n) (T : 𝓞 F) (hT0 : T ≠ 0)
    (hT2 : T ∉ v.asIdeal ^ 2) (ν : ℕ) :
    (if T ∈ v.asIdeal then 1 - 1 / N𝔭 ^ (n - 1) else
        1 + (DVR.chiDiscT (Qp v Q) (ι v T) : ℝ) / N𝔭 ^ ((n - 1) / 2)) *
      (if T ∉ v.asIdeal ∧ DVR.chiDiscT (Qp v Q) (ι v T) = 1 then
        (1 - 1 / N𝔭 ^ ((n - 1) / 2)) / (1 - 1 / N𝔭 ^ (n - 2)) else 1) ≤
      localDensity v Q (unif v ^ (2 * ν) * T) := by
  have h := DVR.localDensity_ge_odd_of_unimodular (Qp v Q) (π v) (irreducible_π v) (π_not_dvd_two v h2)
    (π_not_dvd_det_of_notDvdLevel v Q h2 hN) hn hodd (ι v T) (ι_ne_zero v hT0) (by rwa [π_pow_dvd_ι_iff]) ν
  simp only [q_completion, π_dvd_ι_iff] at h
  rw [localDensity_eq_completion, map_mul, map_pow]
  convert h using 2

end NonDyadic

/-- **$n = 3$ over $F$, non-dyadic $\mathfrak p \nmid N$:** $\beta_\mathfrak p(T'\varpi^{2\nu}) \ge \beta_\mathfrak p(T')$ (first part of
Thm 5.7(a), p. 374). -/
@[kb "hanke2004" "Thm 5.7(a), p. 374 (over F, p ∤ 2N, n = 3, general Q)"]
theorem localDensity_ge_three_of_unimodular (Q : QuadForm (𝓞 F) 3) (h2 : (2 : 𝓞 F) ∉ v.asIdeal)
    (hN : NotDvdLevel v Q) (T : 𝓞 F) (hT0 : T ≠ 0) (hT2 : T ∉ v.asIdeal ^ 2) (ν : ℕ) :
    localDensity v Q T ≤ localDensity v Q (unif v ^ (2 * ν) * T) := by
  rw [localDensity_eq_completion, localDensity_eq_completion, map_mul, map_pow]
  exact DVR.localDensity_ge_three_of_unimodular (Qp v Q) (π v) (irreducible_π v) (π_not_dvd_two v h2)
    (π_not_dvd_det_of_notDvdLevel v Q h2 hN) (ι v T) (ι_ne_zero v hT0) (by rwa [π_pow_dvd_ι_iff]) ν


/-! ### Dyadic $\mathfrak p \nmid N$ -/

section Dyadic

variable (Q : QuadForm (𝓞 F) n) (h2 : (2 : 𝓞 F) ∈ v.asIdeal) (hN : NotDvdLevel v Q)
include h2 hN

/-- **At dyadic $\mathfrak p \nmid N$, $Q \otimes \mathfrak o_\mathfrak p$ is an even unimodular `pairSumForm`** up to $\mathrm{GL}_n(\mathfrak o_\mathfrak p)$
(any ramification). From `DVR.exists_pairSum_of_isLocalLevel_zero`. -/
@[kb "hanke2004" "Lemma 2.1, Lemma 2.2, p. 355–356 (dyadic p ∤ N, over F)"]
theorem exists_pairSum_of_notDvdLevel :
    ∃ (r : ℕ) (A : Fin r → 𝔬 × 𝔬 × 𝔬) (h : r * 2 = n), (∀ i, ¬ π v ∣ (A i).2.1) ∧
      DVR.IsGLEquiv (Qp v Q) (h ▸ DVR.pairSumForm A) :=
  DVR.exists_pairSum_of_isLocalLevel_zero (Qp v Q) (irreducible_π v) (π_dvd_two v h2) (two_ne_zero' v) hN

/-- **Table 1 over $F$ at dyadic $\mathfrak p \nmid N$** (general $Q$, $n \ge 1$, so $n = 2r$): with $\varepsilon$ the Arf sign,
$r_\mathfrak p(s) = N\mathfrak p^{n-1} + \varepsilon(N\mathfrak p^{n/2} - N\mathfrak p^{n/2-1})$ for $s \in \mathfrak p$ and
$N\mathfrak p^{n-1} - \varepsilon N\mathfrak p^{n/2-1}$ for $s \notin \mathfrak p$. -/
@[kb "hanke2004" "Table 1, p. 363 (over F, dyadic p ∤ N, general Q)"]
theorem card_mod_p_of_level_zero_dyadic (hn : 1 ≤ n) (s : 𝓞 F) :
    (s ∈ v.asIdeal → (repCount v Q 1 s : ℤ) = (Ideal.absNorm v.asIdeal : ℤ) ^ (n - 1) +
      DVR.arfSignQ (Qp v Q) (π v) *
        ((Ideal.absNorm v.asIdeal : ℤ) ^ (n / 2) - (Ideal.absNorm v.asIdeal : ℤ) ^ (n / 2 - 1))) ∧
    (s ∉ v.asIdeal → (repCount v Q 1 s : ℤ) = (Ideal.absNorm v.asIdeal : ℤ) ^ (n - 1) -
      DVR.arfSignQ (Qp v Q) (π v) * (Ideal.absNorm v.asIdeal : ℤ) ^ (n / 2 - 1)) := by
  have h := DVR.card_mod_pi_of_level_zero_dyadic (Qp v Q) (irreducible_π v) (π_dvd_two v h2)
    (two_ne_zero' v) hN hn (ι v s)
  simpa only [repCount_eq_completion, q_completion, π_dvd_ι_iff] using h

/-- **Remark 3.5.1 over $F$ at dyadic $\mathfrak p \nmid N$** (general $Q$, $n \ge 3$): every $m$ is locally represented. -/
@[kb "hanke2004" "Remark 3.5.1, p. 362 (over F, dyadic p ∤ N, general Q)"]
theorem isLocallyRepresentedAt_of_level_zero_dyadic (hn : 3 ≤ n) (m : 𝓞 F) :
    IsLocallyRepresentedAt v Q m := by
  rw [isLocallyRepresentedAt_iff]
  exact DVR.isLocallyRepresentedAt_of_level_zero_dyadic (Qp v Q) (irreducible_π v) (π_dvd_two v h2)
    (two_ne_zero' v) hN hn (ι v m)

/-- **Table 2 over $F$ at dyadic $\mathfrak p \nmid N$, $T' \notin \mathfrak p$** (general $Q$, $\Phi_n := \varepsilon$):
$C_\mathfrak p(T') = \dfrac{N\mathfrak p^{n/2-1}}{N\mathfrak p^{n/2-1} - \varepsilon}$. -/
@[kb "hanke2004" "Table 2, p. 370 (over F, dyadic p ∤ N, general Q)"]
theorem table2_unit_of_level_zero_dyadic (hn : 3 ≤ n) (T : 𝓞 F) (hT : T ∉ v.asIdeal) :
    localConstC v Q T = N𝔭 ^ (n / 2 - 1) / (N𝔭 ^ (n / 2 - 1) - DVR.arfSignQ (Qp v Q) (π v)) := by
  rw [localConstC_eq_completion, DVR.table2_unit_of_level_zero_dyadic (Qp v Q) (irreducible_π v)
    (π_dvd_two v h2) (two_ne_zero' v) hN hn (ι v T) (by rwa [π_dvd_ι_iff]), q_completion]

/-- **Table 2 over $F$ at dyadic $\mathfrak p \nmid N$, $T' \in \mathfrak p \setminus \mathfrak p^2$** ((5.9)):
$C_\mathfrak p(T') = \dfrac{N\mathfrak p^{n-2}}{N\mathfrak p^{n-2} - 1}$. -/
@[kb "hanke2004" "Table 2, p. 370; (5.9) (over F, dyadic p ∤ N, general Q)"]
theorem table2_ord_one_of_level_zero_dyadic (hn : 3 ≤ n) (T : 𝓞 F) (hT1 : T ∈ v.asIdeal)
    (hT2 : T ∉ v.asIdeal ^ 2) : localConstC v Q T = N𝔭 ^ (n - 2) / (N𝔭 ^ (n - 2) - 1) := by
  rw [localConstC_eq_completion, DVR.table2_ord_one_of_level_zero_dyadic (Qp v Q) (irreducible_π v)
    (π_dvd_two v h2) (two_ne_zero' v) hN hn (ι v T) (by rwa [π_dvd_ι_iff]) (by rwa [π_pow_dvd_ι_iff]),
    q_completion]

/-- **(5.12), corrected, over $F$ at dyadic $\mathfrak p \nmid N$** (general $Q$): for $T' \notin \mathfrak p^2$,
$C'_\mathfrak p(T') = 1 \iff T' \in \mathfrak p$ or $\varepsilon = 1$, and $C'_\mathfrak p(T') = \frac{X}{X+1}$ ($X = N\mathfrak p^{n/2-1}$) otherwise. -/
@[kb "hanke2004" "(5.12), p. 371 (corrected; over F, dyadic p ∤ N, general Q)"]
theorem localConstC'_of_level_zero_dyadic (hn : 3 ≤ n) (T : 𝓞 F) (hT2 : T ∉ v.asIdeal ^ 2) :
    (T ∈ v.asIdeal → localConstC' v Q T = 1) ∧
    (T ∉ v.asIdeal → DVR.arfSignQ (Qp v Q) (π v) = 1 → localConstC' v Q T = 1) ∧
    (T ∉ v.asIdeal → DVR.arfSignQ (Qp v Q) (π v) = -1 →
      localConstC' v Q T = N𝔭 ^ (n / 2 - 1) / (N𝔭 ^ (n / 2 - 1) + 1)) ∧
    (localConstC' v Q T = 1 ↔ T ∈ v.asIdeal ∨ DVR.arfSignQ (Qp v Q) (π v) = 1) := by
  have h := DVR.localConstC'_of_level_zero_dyadic (Qp v Q) (irreducible_π v) (π_dvd_two v h2)
    (two_ne_zero' v) hN hn (ι v T) (by rwa [π_pow_dvd_ι_iff])
  simpa only [← localConstC'_eq_completion, q_completion, π_dvd_ι_iff] using h

open Classical in
/-- **Per-place lower bound L10 over $F$ at dyadic $\mathfrak p \nmid N$** (proof of Thm 5.7(b),(c), p. 374; general $Q$):
$\beta_\mathfrak p(m) \ge (1 - \varepsilon N\mathfrak p^{-n/2})\frac{X-1}{X+1}$ if $\varepsilon = -1$ and $m \in \mathfrak p$, and
$\ge 1 - \varepsilon N\mathfrak p^{-n/2}$ otherwise ($X = N\mathfrak p^{n/2-1}$). -/
@[kb "hanke2004" "Proof of Thm 5.7(b),(c), p. 374 (over F, dyadic p ∤ N, general Q)"]
theorem localDensity_ge_of_level_zero_dyadic (hn : 3 ≤ n) (m : 𝓞 F) (hm : m ≠ 0) :
    (1 - (DVR.arfSignQ (Qp v Q) (π v) : ℝ) / N𝔭 ^ (n / 2)) *
        (if DVR.arfSignQ (Qp v Q) (π v) = -1 ∧ m ∈ v.asIdeal then
          (N𝔭 ^ (n / 2 - 1) - 1) / (N𝔭 ^ (n / 2 - 1) + 1) else 1) ≤
      localDensity v Q m := by
  have h := DVR.localDensity_ge_of_level_zero_dyadic (Qp v Q) (irreducible_π v) (π_dvd_two v h2)
    (two_ne_zero' v) hN hn (ι v m) (ι_ne_zero v hm)
  simp only [q_completion, π_dvd_ι_iff, ← localDensity_eq_completion] at h
  convert h using 2

end Dyadic

/-- **Remark 3.8.1 over $F$** (Hanke 2004, p. 364): if $\mathfrak p \nmid N$ and $n \ge 3$, then $Q$ is isotropic over $F_\mathfrak p$, at
every finite prime (dyadic or not). From `DVR.isotropicIn_of_isLocalLevel_zero` (uses `NF.isAdicComplete`). -/
@[kb "hanke2004" "Remark 3.8.1, p. 364 (over F)"]
theorem isotropicIn_of_notDvdLevel (Q : QuadForm (𝓞 F) n) (hN : NotDvdLevel v Q) (hn : 3 ≤ n) :
    Q.IsotropicIn Fv := by
  rw [← isotropicIn_Qp_iff]
  exact DVR.isotropicIn_of_isLocalLevel_zero Fv (Qp v Q) (irreducible_π v) (two_ne_zero' v) hN hn

end QuadFormsKB.LocalDensity.NF
