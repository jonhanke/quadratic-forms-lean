/-
# Hanke 2011, §2–§4: local genera of primitive $\mathcal O_{\mathfrak p}$-valued forms

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`).

**Setting.** $R$ is a discrete valuation ring (in the paper $R = \mathcal O_{\mathfrak p}$, the completion of the ring of
integers of a number field at a finite prime $\mathfrak p$, with uniformizer $\pi$ and residue field $\mathbb F$ of order
$q$). A quadratic form in $n$ variables is `QuadForm R n` (upper-triangular coefficients $c_{ij}$, $i \le j$,
variables $x_0,\dots,x_{n-1}$; 0-based). Its **Hessian matrix** is $H = C + C^{\mathsf T}$ (`QuadForm.hessian`) and the
**Hessian determinant** is $\det H$. A form is **primitive** if its coefficients generate the unit ideal
(`IsPrimitiveForm`). Two forms are in the same **local genus** if they are isometric over $R$, i.e. $Q'(x) = Q(gx)$
for some $g \in \mathrm{GL}_n(R)$ (`QuadFormsKB.Siegel.IsometricGL`). The **Hessian determinant squareclass** of $Q$
is the class of $\det H(Q)$ modulo $(R^\times)^2$. The ideal $h_n$ (Lemma 2.5, see `HessianParity.lean`) is $R$ for $n$
even and $2R$ for $n$ odd; a squareclass $S$ is **normalized** if $\mathrm{ord}_R(S) = \mathrm{ord}_R(h_n)$
(`IsNormalizedHessian`: $\mathrm{ord}(\det H) = 0$ for $n$ even and $= \mathrm{ord}(2)$ for $n$ odd).

**Contents.**
* `UniqueNormalizedLocalGenus R n` (Thm. 2.6, p. 8): the statement, for all primes, that there is at most one local genus
  of primitive $R$-valued forms in $n$ variables with a given normalized Hessian determinant squareclass.
  It is a named `Prop` structure (never an axiom). The nondyadic case (2 a unit in $R$) is **proved**
  (`uniqueNormalizedLocalGenus_of_isUnit_two`, from `isometricGL_of_unimodular_dvr`), and specialized to the completion
  at a prime $\mathfrak p \nmid 2$ of a number field (`uniqueNormalizedLocalGenus_completion`). The dyadic case is proved in the
  paper with O'Meara 93:15, 93:18, 93:28, which the repository does not yet have in usable form, so it is **not proved here**.
* Lemma 4.7 (p. 16), the two facts it rests on, for $\mathfrak p \nmid 2$: (a) a unimodular form is $R$-isometric to
  $\langle 1,\dots,1,d\rangle$ with $d$ a unit, and its Hasse invariant (Serre's convention $\prod_{i<j}(a_i,a_j)$,
  computed over any field $K \supseteq R$) is $1$, because the Hilbert symbol of two units is $1$
  (`hilbertSymbol_units_dvr`, `hasseLocal_unit_diag`, `lemma_4_7_unimodular`, `lemma_4_7_exists_with_det`); (b)
  $\det H(Q) \in R$ for an $R$-valued form, so no $R$-valued form has Hessian determinant squareclass of negative order
  (`no_form_of_negative_order`).
* Lemma 3.6 (proof, p. 13): the self-density of a unimodular form at $\mathfrak p \nmid 2$ in the paper's normalization
  $\beta_{G,\mathfrak p}(G) = \tfrac12\,\alpha_{\mathfrak p}(Q,Q)$ (`lemma_3_6_density_odd`, `lemma_3_6_density_even`), and a
  check of the sign convention for $n$ even (`chiDisc_even`, `density_binary_unit_diag`, `chi_neg_one_zmod_three`).

**Normalization (important).** The repository's `localDensityForm Q Q π` is the full local density
$\alpha_{\mathfrak p}(Q,Q)$ counting the orthogonal group (so it equals $2\prod_{i=1}^m(1-q^{-2i})$ for $n = 2m+1$ unimodular,
$\mathfrak p \nmid 2$; e.g. $2$ for $n = 1$). The paper's $\beta_{G,\mathfrak p}(G)$ is half of it (the product
$\prod(1-q^{-2i})$ without the factor $2$ of $|O| = 2|SO|$), so $\beta = \alpha/2$ here.

**Updates and errata found** (proposed by the formalization,
not yet confirmed by the author):
* *Update (typographical), Sublemma 2.9:* it is stated "Suppose that $n \in \mathbb N$ is even", but its proof
  ($L = L_0 \oplus L_1$ with $L_1$ the rank-one lattice $2ux^2$) is the **odd** case; it should read "$n$ is odd".
* *Erratum (sign), Lemma 3.6 / the even-$n$ density:* with the literal reading "$\pm = -\chi_{\mathfrak p}(S_{\mathfrak p})$"
  for $S_{\mathfrak p} = \det H$ and $n = 2r$, the factor $(1 \pm q^{-r})$ is wrong in general: the correct character is
  $\chi((-1)^r \det H)$ (`chiDisc_even`). Counterexample: $Q = x^2+y^2$ at $q = 3$ (`density_binary_unit_diag`,
  `chi_neg_one_zmod_three`). See the docstring of `density_binary_unit_diag`.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Lattices.UnimodularDVR
import QuadFormsKB.Tamagawa.OrthFq
import QuadFormsKB.LocalDensity.NFBridge
import QuadFormsKB.Literature.Hanke2011Structure.HasseScaling

open Matrix IsDedekindDomain NumberField

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Hanke2011Structure

section Statements

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}

/-- **Primitive $R$-valued quadratic form:** the coefficients $c_{ij}$ ($0 \le i, j < n$; only $i \le j$ can be nonzero) of
$Q \in$ `QuadForm R n` generate the unit ideal of $R$. (For $n = 0$ the ideal is $0$, so no form in $0$ variables is
primitive.) -/
def IsPrimitiveForm (Q : QuadForm R n) : Prop :=
  Ideal.span (Set.range fun p : Fin n × Fin n => Q.coeff p.1 p.2) = ⊤

variable (R) in
/-- **Normalized Hessian determinant:** $\mathrm{ord}_R(\det H(Q)) = \mathrm{ord}_R(h_n)$, where $h_n = R$ for $n$ even
and $h_n = 2R$ for $n$ odd (Hanke 2011, Lemma 2.5). Here `addVal R` is the additive valuation of the DVR $R$
with values in $\mathbb N \cup \{\infty\}$ (so $\det H = 0$ is never normalized). -/
def IsNormalizedHessian (Q : QuadForm R n) : Prop :=
  IsDiscreteValuationRing.addVal R Q.hessian.det =
    if Even n then 0 else IsDiscreteValuationRing.addVal R (2 : R)

variable (R n) in
/-- **Theorem 2.6 (Uniqueness of normalized local genera; Hanke 2011, p. 8).** Let $R$ be a DVR (the paper:
$R = \mathcal O_{\mathfrak p}$) and $n \in \mathbb N$. If $S$ is a Hessian determinant squareclass with
$\mathrm{ord}_R(S) = \mathrm{ord}_R(h_n)$, there is at most one local genus of primitive $R$-valued quadratic forms in $n$
variables with Hessian determinant squareclass $S$. Explicitly: for primitive $Q, Q' \in$ `QuadForm R n` with
$\mathrm{ord}_R(\det H(Q)) = \mathrm{ord}_R(h_n)$ and $\det H(Q') = u^2\det H(Q)$ for a unit $u \in R^\times$, the forms
$Q$ and $Q'$ are isometric over $R$ (`QuadFormsKB.Siegel.IsometricGL`).

This is a `Prop` structure so that the (dyadic) cases that are not yet proved can be named as an input rather than assumed
silently. It is proved when $2 \in R^\times$ (`uniqueNormalizedLocalGenus_of_isUnit_two`); the dyadic case
(O'Meara 93:15, 93:18, 93:28) is not proved in the repository. -/
@[kb "hanke2011structure" "Thm. 2.6, p. 8"]
structure UniqueNormalizedLocalGenus : Prop where
  unique : ∀ Q Q' : QuadForm R n, IsPrimitiveForm Q → IsPrimitiveForm Q' → IsNormalizedHessian R Q →
    ∀ u : R, IsUnit u → Q'.hessian.det = u ^ 2 * Q.hessian.det → QuadFormsKB.Siegel.IsometricGL Q Q'

end Statements

section Nondyadic

open QuadFormsKB.Lattices.Nbr QuadFormsKB.LocalDensity

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}
  [Fintype (IsLocalRing.ResidueField R)] [DecidableEq (IsLocalRing.ResidueField R)]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

/-- A unit is not divisible by a uniformizer (irreducible element). -/
private lemma not_dvd_of_isUnit' {π u : R} (hπ : Irreducible π) (hu : IsUnit u) : ¬ π ∣ u :=
  DVR.dvr_not_dvd_of_isUnit hπ hu

/-- **Theorem 2.6, nondyadic case ($2 \in R^\times$; Hanke 2011, p. 8).** Let $R$ be a complete DVR with finite residue
field in which $2$ is a unit. Then `UniqueNormalizedLocalGenus R n` holds for every $n$: for $Q, Q'$ primitive with
$\mathrm{ord}(\det H(Q)) = \mathrm{ord}(h_n)$ (which is $0$ in both parities, as $2$ is a unit, so $\det H(Q)$ is a unit)
and $\det H(Q') = u^2 \det H(Q)$, $u$ a unit, the forms are isometric over $R$. *Proof:* `isometricGL_of_unimodular_dvr`
(O'Meara 92:1); primitivity is not used. -/
@[kb "hanke2011structure" "Thm. 2.6, p. 8 (p ∤ 2)"]
theorem uniqueNormalizedLocalGenus_of_isUnit_two (h2 : IsUnit (2 : R)) : UniqueNormalizedLocalGenus R n := by
  refine ⟨fun Q Q' _ _ hnorm u hu hdet => ?_⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπ2 : ¬ π ∣ 2 := not_dvd_of_isUnit' hπ h2
  have hz : IsDiscreteValuationRing.addVal R Q.hessian.det = 0 := by
    unfold IsNormalizedHessian at hnorm
    rw [hnorm]
    split_ifs
    · rfl
    · exact IsDiscreteValuationRing.addVal_eq_zero_iff.mpr h2
  have hQ : ¬ π ∣ Q.hessian.det := not_dvd_of_isUnit' hπ (IsDiscreteValuationRing.addVal_eq_zero_iff.mp hz)
  exact isometricGL_of_unimodular_dvr hπ hπ2 Q Q' hQ hu hdet

/-- **Theorem 2.6 for the completion of a number field at $\mathfrak p \nmid 2$** (Hanke 2011, p. 8). For a number field
$F$ and a finite prime $\mathfrak p$ (`v`) with $2 \notin \mathfrak p$, `UniqueNormalizedLocalGenus` holds for
$R = \mathcal O_{\mathfrak p}$ = `v.adicCompletionIntegers F`, in every dimension $n$. -/
@[kb "hanke2011structure" "Thm. 2.6, p. 8 (p ∤ 2, number field completion)"]
theorem uniqueNormalizedLocalGenus_completion {F : Type*} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (n : ℕ) :
    UniqueNormalizedLocalGenus (v.adicCompletionIntegers F) n := by
  apply uniqueNormalizedLocalGenus_of_isUnit_two
  have hnd : ¬ LocalDensity.NF.π v ∣ (2 : v.adicCompletionIntegers F) := by
    have := (LocalDensity.NF.π_pow_dvd_ι_iff v 1 2).not.mpr (by rwa [pow_one])
    rwa [pow_one, map_ofNat] at this
  exact DVR.dvr_isUnit_of_not_dvd (LocalDensity.NF.irreducible_π v) hnd

end Nondyadic

section Lemma47

open QuadFormsKB.Lattices.Nbr QuadFormsKB.LocalDensity

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}
  [Fintype (IsLocalRing.ResidueField R)] [DecidableEq (IsLocalRing.ResidueField R)]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
  {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
include hπ h2

/-- **The Hilbert symbol of two units is $1$ at a nondyadic prime** (the fact behind Hanke 2011, Lemma 4.7, p. 16).
Let $R$ be a complete DVR with finite residue field, $\pi \nmid 2$, and $K$ any field containing $R$ (e.g. its fraction
field $F_{\mathfrak p}$). For units $a, b \in R^\times$, $(a, b)_K = 1$. *Proof:* `exists_binary_one_dvr` gives
$x, y \in R$ with $ax^2 + by^2 = 1$, i.e. the conic $z^2 = ax^2+by^2$ has the nonzero solution $(x, y, 1)$. -/
@[kb "hanke2011structure" "Lemma 4.7, p. 16"]
theorem hilbertSymbol_units_dvr (K : Type*) [Field K] [Algebra R K] {a b : R} (ha : IsUnit a) (hb : IsUnit b) :
    QuadFormsKB.hilbertSymbol K (algebraMap R K a) (algebraMap R K b) = 1 := by
  obtain ⟨x, y, h⟩ := exists_binary_one_dvr hπ h2 ha hb
  have h' := congrArg (algebraMap R K) h
  simp only [map_add, map_mul, map_pow, map_one] at h'
  have hex : ∃ x' y' z' : K, (x', y', z') ≠ 0 ∧
      z' ^ 2 = algebraMap R K a * x' ^ 2 + algebraMap R K b * y' ^ 2 := by
    refine ⟨algebraMap R K x, algebraMap R K y, 1, ?_, ?_⟩
    · intro h0
      have := congrArg (fun t : K × K × K => t.2.2) h0
      simp at this
    · rw [one_pow]; exact h'.symm
  unfold QuadFormsKB.hilbertSymbol
  simp only [hex, ↓reduceIte]

/-- **The Hasse invariant of a unit diagonal form is $1$** (Hanke 2011, Lemma 4.7, p. 16). With
$K \supseteq R$ a field and $a_0,\dots,a_{k-1} \in R^\times$,
$c_K(\langle a_0,\dots,a_{k-1}\rangle) = \prod_{i<j}(a_i,a_j)_K = 1$ (`hasseLocal`, Serre's convention). -/
@[kb "hanke2011structure" "Lemma 4.7, p. 16"]
theorem hasseLocal_unit_diag (K : Type*) [Field K] [Algebra R K] {k : ℕ} (a : Fin k → R)
    (ha : ∀ i, IsUnit (a i)) : hasseLocal K (fun i => algebraMap R K (a i)) = 1 := by
  unfold hasseLocal
  refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => ?_
  split_ifs
  · exact hilbertSymbol_units_dvr hπ h2 K (ha i) (ha j)
  · rfl

/-- **Lemma 4.7, fact (a): a unimodular form has a unit diagonalization with Hasse invariant $1$** (Hanke 2011, p. 16;
$\mathfrak p \nmid 2$). Let $R$ be a complete DVR with finite residue field, $\pi \nmid 2$, $K \supseteq R$ a field, and
$Q \in$ `QuadForm R n` with $\pi \nmid \det H(Q)$. Then $Q$ is $R$-isometric to $\langle a_0,\dots,a_{n-1}\rangle$ with
all $a_i \in R^\times$, and $c_K(\langle a_i \rangle) = 1$. -/
@[kb "hanke2011structure" "Lemma 4.7, p. 16"]
theorem lemma_4_7_diag (K : Type*) [Field K] [Algebra R K] (Q : QuadForm R n) (hdet : ¬ π ∣ Q.hessian.det) :
    ∃ a : Fin n → R, (∀ i, IsUnit (a i)) ∧ QuadFormsKB.Siegel.IsometricGL Q (QuadForm.diag a) ∧
      hasseLocal K (fun i => algebraMap R K (a i)) = 1 := by
  obtain ⟨a, ha, hE, _⟩ := DVR.exists_diag_of_unimodular Q π hπ h2 hdet
  have haU : ∀ i, IsUnit (a i) := fun i => DVR.dvr_isUnit_of_not_dvd hπ (ha i)
  exact ⟨a, haU, Siegel.Kneser.isometricGL_of_isGLEquiv hE, hasseLocal_unit_diag hπ h2 K a haU⟩

/-- **Lemma 4.7, fact (a), normal form $\langle 1,\dots,1,d\rangle$** (Hanke 2011, p. 16; $\mathfrak p \nmid 2$). With the
hypotheses of `lemma_4_7_diag` and $n = k+1$, there is a unit $d \in R^\times$ such that $Q$ is $R$-isometric to
$\langle 1,\dots,1,d\rangle$ (last coefficient $d$, index $k$), and the Hasse invariant of $\langle 1,\dots,1,d\rangle$
is $1$. -/
@[kb "hanke2011structure" "Lemma 4.7, p. 16"]
theorem lemma_4_7_normal_form (K : Type*) [Field K] [Algebra R K] {k : ℕ} (Q : QuadForm R (k + 1))
    (hdet : ¬ π ∣ Q.hessian.det) :
    ∃ d : R, IsUnit d ∧
      QuadFormsKB.Siegel.IsometricGL Q (QuadForm.diag (Function.update (1 : Fin (k + 1) → R) (Fin.last k) d)) ∧
      hasseLocal K (fun i => algebraMap R K (Function.update (1 : Fin (k + 1) → R) (Fin.last k) d i)) = 1 := by
  obtain ⟨a, haU, hiso, _⟩ := lemma_4_7_diag hπ h2 K Q hdet
  have hd : IsUnit (∏ i, a i) := IsUnit.prod_iff.mpr fun i _ => haU i
  have hU : ∀ i, IsUnit (Function.update (1 : Fin (k + 1) → R) (Fin.last k) (∏ i, a i) i) := by
    intro i
    by_cases hi : i = Fin.last k
    · subst hi; rw [Function.update_self]; exact hd
    · rw [Function.update_of_ne hi]; exact isUnit_one
  exact ⟨∏ i, a i, hd, hiso.trans (isometricGL_diag_normal_dvr hπ h2 a haU), hasseLocal_unit_diag hπ h2 K _ hU⟩

/-- **Lemma 4.7, existence and uniqueness of the unimodular genus** (Hanke 2011, p. 16; $\mathfrak p \nmid 2$,
$\mathrm{ord}(S) = 0$, $n = k+1 \ge 1$). For every unit $s \in R^\times$ there is a form $Q_s$ in $k+1$ variables with
$\det H(Q_s) = s$ and Hasse invariant $1$ (it is $\langle 1,\dots,1,s/2^{k+1}\rangle$), and every $Q'$ with
$\det H(Q') = u^2 s$, $u$ a unit, is $R$-isometric to $Q_s$. So the number of local genera with squareclass $[s]$ is
exactly $1$ (the paper's $A^*_{p;n}(S_p) = B^*_{p;n}(S_p) = 1$ counts this genus, with $c_p = 1$). -/
@[kb "hanke2011structure" "Lemma 4.7, p. 16"]
theorem lemma_4_7_exists_with_det (K : Type*) [Field K] [Algebra R K] {k : ℕ} {s : R} (hs : IsUnit s) :
    ∃ Q : QuadForm R (k + 1), Q.hessian.det = s ∧
      (∃ a : Fin (k + 1) → R, (∀ i, IsUnit (a i)) ∧ QuadFormsKB.Siegel.IsometricGL Q (QuadForm.diag a) ∧
        hasseLocal K (fun i => algebraMap R K (a i)) = 1) ∧
      ∀ (Q' : QuadForm R (k + 1)) (u : R), IsUnit u → Q'.hessian.det = u ^ 2 * s →
        QuadFormsKB.Siegel.IsometricGL Q Q' := by
  have h2u : IsUnit (2 : R) := DVR.dvr_isUnit_of_not_dvd hπ h2
  have h2k : IsUnit ((2 : R) ^ (k + 1)) := h2u.pow _
  obtain ⟨w, hw⟩ := h2k
  let d : R := s * ↑w⁻¹
  have hdU : IsUnit d := hs.mul (Units.isUnit _)
  let Q : QuadForm R (k + 1) := QuadForm.diag (Function.update (1 : Fin (k + 1) → R) (Fin.last k) d)
  have hQ : Q.hessian.det = s := by
    show (QuadForm.diag _).hessian.det = s
    rw [DVR.det_hessian_diag, Finset.prod_update_of_mem (Finset.mem_univ _)]
    simp only [Pi.one_apply, Finset.prod_const_one, mul_one, d]
    rw [← hw, mul_comm s, ← mul_assoc, Units.mul_inv, one_mul]
  have hQU : ¬ π ∣ Q.hessian.det := by rw [hQ]; exact DVR.dvr_not_dvd_of_isUnit hπ hs
  refine ⟨Q, hQ, ?_, fun Q' u hu hdet => ?_⟩
  · have hU : ∀ i, IsUnit (Function.update (1 : Fin (k + 1) → R) (Fin.last k) d i) := by
      intro i
      by_cases hi : i = Fin.last k
      · subst hi; rw [Function.update_self]; exact hdU
      · rw [Function.update_of_ne hi]; exact isUnit_one
    exact ⟨_, hU, QuadFormsKB.Siegel.IsometricGL.refl _, hasseLocal_unit_diag hπ h2 K _ hU⟩
  · exact isometricGL_of_unimodular_dvr hπ h2 Q Q' hQU hu (by rw [hdet, hQ])

end Lemma47

section NegativeOrder

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}

/-- **Lemma 4.7, fact (b): no $R$-valued form has Hessian determinant squareclass of negative order** (Hanke 2011, p. 16;
holds over every DVR). Let $K$ be a field containing $R$ and $s \in K$ not in (the image of) $R$, i.e. of negative
$R$-order. Then for every $Q \in$ `QuadForm R n` and unit $u \in R^\times$,
$\det H(Q) \ne u^2 s$ in $K$; equivalently the squareclass $[s]$ is not the Hessian determinant squareclass of any
$R$-valued form, so $A^*_{p;n}(S_p) = B^*_{p;n}(S_p) = 0$ when $\mathrm{ord}_p(S_p) < 0$. -/
@[kb "hanke2011structure" "Lemma 4.7, p. 16"]
theorem no_form_of_negative_order (K : Type*) [Field K] [Algebra R K] {s : K}
    (hs : s ∉ (algebraMap R K).range) (Q : QuadForm R n) (u : Rˣ) :
    algebraMap R K Q.hessian.det ≠ (algebraMap R K (u : R)) ^ 2 * s := by
  intro h
  apply hs
  refine ⟨(↑u⁻¹ : R) ^ 2 * Q.hessian.det, ?_⟩
  have hu : algebraMap R K (↑u⁻¹ : R) * algebraMap R K (u : R) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  rw [map_mul, map_pow, h]
  calc algebraMap R K ↑u⁻¹ ^ 2 * (algebraMap R K ↑u ^ 2 * s)
      = (algebraMap R K ↑u⁻¹ * algebraMap R K ↑u) ^ 2 * s := by ring
    _ = s := by rw [hu]; ring

end NegativeOrder

section Density

open QuadFormsKB.LocalDensity

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Fintype (IsLocalRing.ResidueField R)] [DecidableEq (IsLocalRing.ResidueField R)]
  {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
include hπ h2

/-- **Lemma 3.6, density at a good prime, odd $n$ (Hanke 2011, p. 13; paper's normalization).** Let $R$ be a DVR with
finite residue field of order $q$, $\pi \nmid 2$, and $Q \in$ `QuadForm R (2r+1)` with $\pi \nmid \det H(Q)$. In the paper's
normalization $\beta = \alpha/2$ (the repository's `localDensityForm Q Q π` is the full density $\alpha$, counting
$|O| = 2|SO|$),
$$\tfrac12\,\alpha_\pi(Q, Q) = \prod_{i=1}^{r}(1 - q^{-2i}) = \frac{|SO_Q(\mathbb F_q)|}{q^{n(n-1)/2}}.$$
Index shift: the product runs over `i ∈ range r` with exponent `2 * (i + 1)`. -/
@[kb "hanke2011structure" "Lemma 3.6, proof, p. 13"]
theorem lemma_3_6_density_odd (r : ℕ) (Q : QuadForm R (2 * r + 1)) (hdet : ¬ π ∣ Q.hessian.det) :
    DVR.localDensityForm Q Q π / 2 =
      ∏ i ∈ Finset.range r, (1 - ((DVR.q R : ℝ) ^ (2 * (i + 1)))⁻¹) := by
  rw [DVR.localDensityForm_self_odd π r Q hπ h2 hdet]
  ring

/-- **The character of the even-rank density is $\chi((-1)^r\det H)$, not $\chi(\det H)$.** For $n = 2r$,
$2 \in R^\times$ and $\bar d$ the residue of $\det H(Q)$ in $\mathbb F$: `chiDisc Q` $= \chi((-1)^r\bar d)$ with $\chi$ the
quadratic character of $\mathbb F$. (By definition `chiDisc Q` $= \chi((-1)^{\lfloor n/2\rfloor}\bar d/2^n)$ and
$2^{2r} = (2^r)^2$ is a square.) -/
theorem chiDisc_even (r : ℕ) (Q : QuadForm R (2 * r)) :
    DVR.chiDisc Q = quadraticChar (IsLocalRing.ResidueField R)
      ((-1) ^ r * IsLocalRing.residue R Q.hessian.det) := by
  have h2u : IsUnit (2 : R) := DVR.dvr_isUnit_of_not_dvd hπ h2
  have h2F : (2 : IsLocalRing.ResidueField R) ^ r ≠ 0 :=
    pow_ne_zero _ ((h2u.map (IsLocalRing.residue R)).ne_zero)
  unfold DVR.chiDisc DVR.resGramDet
  rw [show 2 * r / 2 = r by omega]
  have : (-1 : IsLocalRing.ResidueField R) ^ r * (IsLocalRing.residue R Q.hessian.det / 2 ^ (2 * r)) =
      ((-1) ^ r * IsLocalRing.residue R Q.hessian.det) * ((2 ^ r)⁻¹) ^ 2 := by
    rw [pow_mul']
    field_simp
  rw [this, map_mul, quadraticChar_sq_one' (inv_ne_zero h2F), mul_one]

/-- **Lemma 3.6, density at a good prime, even $n$ (Hanke 2011, p. 13; paper's normalization).** Let $R$ be a DVR with
finite residue field of order $q$, $\pi \nmid 2$, $r \ge 1$, and $Q \in$ `QuadForm R (2r)` with $\pi \nmid \det H(Q)$.
Then, with $\beta = \alpha/2$ and $\chi_D = \chi((-1)^r\det H(Q))$ (`DVR.chiDisc Q`; see `chiDisc_even`),
$$\tfrac12\,\alpha_\pi(Q, Q) = (1 - \chi_D\,q^{-r})\prod_{i=1}^{r-1}(1 - q^{-2i}).$$
So the factor $(1 \pm q^{-r})$ has $\pm = -\chi((-1)^r\det H)$, with the $(-1)^r$ inside the character. -/
@[kb "hanke2011structure" "Lemma 3.6, proof, p. 13"]
theorem lemma_3_6_density_even (r : ℕ) (hr : 1 ≤ r) (Q : QuadForm R (2 * r)) (hdet : ¬ π ∣ Q.hessian.det) :
    DVR.localDensityForm Q Q π / 2 =
      (1 - (DVR.chiDisc Q : ℝ) * ((DVR.q R : ℝ) ^ r)⁻¹) *
        ∏ i ∈ Finset.range (r - 1), (1 - ((DVR.q R : ℝ) ^ (2 * (i + 1)))⁻¹) := by
  rw [DVR.localDensityForm_self_even π r hr Q hπ h2 hdet]
  ring

/-- **Sign check for $n$ even: the binary form $x^2+y^2$** (Hanke 2011, Lemma 3.6, p. 13; proposed erratum). For
$R$ with $\pi \nmid 2$ and $Q = \langle 1, 1\rangle = x^2+y^2$ (so $\det H = 4$, a square in $R^\times$):
$$\tfrac12\,\alpha_\pi(Q,Q) = 1 - \chi(-1)\,q^{-1}.$$
Since $\det H(Q) = 4$ is a square, the literal reading "$\pm = -\chi_{\mathfrak p}(S_{\mathfrak p})$" with
$S_{\mathfrak p} = \det H$ would give $1 - q^{-1}$, which is wrong when $\chi(-1) = -1$, i.e. $q \equiv 3 \pmod 4$. E.g. $q = 3$:
$x^2+y^2$ is anisotropic over $\mathbb F_3$, $|SO_2(\mathbb F_3)| = q+1 = 4$, so $\beta = 4/q = 1+1/3$
(`chi_neg_one_zmod_three`), not $1-1/3$. The correct character is $\chi((-1)^r\det H)$ (here $r = 1$). -/
@[kb "hanke2011structure" "Lemma 3.6, proof, p. 13"]
theorem density_binary_unit_diag :
    DVR.localDensityForm (QuadForm.diag (![1, 1] : Fin 2 → R)) (QuadForm.diag (![1, 1] : Fin 2 → R)) π / 2 =
      1 - (quadraticChar (IsLocalRing.ResidueField R) (-1) : ℝ) * ((DVR.q R : ℝ))⁻¹ := by
  have hdet : ¬ π ∣ (QuadForm.diag (![1, 1] : Fin 2 → R)).hessian.det := by
    rw [DVR.det_hessian_diag]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one]
    exact DVR.dvr_not_dvd_of_isUnit hπ ((DVR.dvr_isUnit_of_not_dvd hπ h2).pow 2)
  have h := lemma_3_6_density_even hπ h2 1 le_rfl (QuadForm.diag (![1, 1] : Fin 2 → R)) hdet
  have hchi := chiDisc_even hπ h2 1 (QuadForm.diag (![1, 1] : Fin 2 → R))
  rw [DVR.det_hessian_diag] at hchi
  have hp : ∏ i, (![1, 1] : Fin 2 → R) i = 1 := by simp [Fin.prod_univ_two]
  simp only [hp, mul_one, map_pow, map_ofNat, pow_one] at hchi
  have hsq : quadraticChar (IsLocalRing.ResidueField R) (-1 * (2 : IsLocalRing.ResidueField R) ^ 2) =
      quadraticChar (IsLocalRing.ResidueField R) (-1) := by
    have h2F : (2 : IsLocalRing.ResidueField R) ≠ 0 := by
      have := (DVR.dvr_isUnit_of_not_dvd hπ h2).map (IsLocalRing.residue R)
      rw [map_ofNat] at this
      exact this.ne_zero
    rw [map_mul, quadraticChar_sq_one' h2F, mul_one]
  rw [hsq] at hchi
  rw [h, hchi]
  simp

end Density

/-- **$-1$ is a nonsquare mod $3$:** $\chi_3(-1) = -1$ for the quadratic character of $\mathbb F_3$. With
`density_binary_unit_diag` this gives $\beta(x^2+y^2) = 1 + 1/3$ at $q = 3$. -/
theorem chi_neg_one_zmod_three : quadraticChar (ZMod 3) (-1) = -1 := by
  rw [quadraticChar_neg_one_iff_not_isSquare]
  decide

end QuadFormsKB.Hanke2011Structure
