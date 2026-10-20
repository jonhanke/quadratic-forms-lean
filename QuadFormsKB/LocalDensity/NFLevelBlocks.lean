/-
# (2.4) and (2.5) over a number field, at every prime

**Layer:** number field ($Q$ = `QuadForm (𝓞 F) n`, $\mathfrak p$ = `v`, $\mathfrak o_\mathfrak p$ = `v.adicCompletionIntegers F`,
uniformizer $\varpi$ = `π v`, $t = \mathrm{ord}_\mathfrak p 2$ given by $2 \in \mathfrak p^t \setminus \mathfrak p^{t+1}$).
**Proves** Hanke 2004, (2.4) and (2.5), p. 356, over $F$ at every finite prime, with the corrected per-block values of
`DVRLevelBlocks.lean`: $Q \otimes \mathfrak o_\mathfrak p$ is $\mathrm{GL}_n(\mathfrak o_\mathfrak p)$-equivalent to a normal form
`IsJordanFormW` (norm exponents $w$, scale exponents $\mu$), and
* $\det H \in \mathfrak p^k \iff k \le \sum_i \lambda'_i$ (so $\mathrm{ord}_\mathfrak p D_{2Q} = \sum_i \lambda'_i$, `detBlockExp`);
* $\mathrm{ord}_\mathfrak p N = \max_i \lambda''_i$ (`levelBlockExp`; $\mathrm{ord}_\mathfrak p N$ is `DVR.levelExp (Qp v Q) (π v)`).

`NF.eq_2_4_2_5` (every $\mathfrak p$); `NF.eq_2_4_2_5_of_not_sq_dvd_two` ($\mathfrak p^2 \nmid 2$: printed (2.5), (2.4) with
$2\nu_j$); `NF.eq_2_4_2_5_nondyadic` ($\mathfrak p \nmid 2$: verbatim).
**Depends on** `DVRLevelBlocks.lean`, `NFLocalGeneral.lean`.
-/
import QuadFormsKB.LocalDensity.DVRLevelBlocks
import QuadFormsKB.LocalDensity.NFLocalGeneral

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.LocalDensity.NF

open QuadForm

variable {F : Type*} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

local notation "𝔬" => v.adicCompletionIntegers F

/-- $2 = \varpi^t\cdot$unit in $\mathfrak o_\mathfrak p$ when $2 \in \mathfrak p^t \setminus \mathfrak p^{t+1}$. -/
theorem two_eq_pow_mul_unit {t : ℕ} (ht : (2 : 𝓞 F) ∈ v.asIdeal ^ t) (ht' : (2 : 𝓞 F) ∉ v.asIdeal ^ (t + 1)) :
    ∃ u : 𝔬, IsUnit u ∧ (2 : 𝔬) = π v ^ t * u := by
  obtain ⟨u, hu, hu1⟩ := DVR.dvr_exact (irreducible_π v) ((π_pow_dvd_two_iff v t).2 ht)
    (fun h => ht' ((π_pow_dvd_two_iff v (t + 1)).1 h))
  exact ⟨u, hu1, hu⟩

/-- $\det H \in \mathfrak p^k \iff k \le s$ when $\det H = \varpi^s\cdot$unit in $\mathfrak o_\mathfrak p$. -/
theorem det_mem_pow_iff (Q : QuadForm (𝓞 F) n) {s : ℕ} {u : 𝔬} (hu : IsUnit u)
    (h : (Qp v Q).hessian.det = π v ^ s * u) (k : ℕ) : Q.hessian.det ∈ v.asIdeal ^ k ↔ k ≤ s := by
  rw [← π_pow_dvd_ι_iff, ← det_hessian_Qp, h, hu.dvd_mul_right,
    pow_dvd_pow_iff (irreducible_π v).ne_zero (irreducible_π v).not_isUnit]

/-- **(2.4) and (2.5) over $F$, corrected, at every finite prime** (Hanke 2004, p. 356): for $Q$ nondegenerate and
$t = \mathrm{ord}_\mathfrak p 2$, $Q \otimes \mathfrak o_\mathfrak p$ is equivalent to a normal form `IsJordanFormW Q' ϖ P w` with
scale exponents $\mu$, and $\det H \in \mathfrak p^k \iff k \le \sum_i \lambda'_i$ (`DVR.detBlockExp`: $w_i + t$ on
1-dimensional blocks, $\mu_j$ per coordinate of a 2-dimensional block), $\mathrm{ord}_\mathfrak p N = \max_i \lambda''_i$
(`DVR.levelBlockExp`: $w_i + 2t$, resp. $2\mu_j - w_j$). From `DVR.eq_2_4_2_5_general`. -/
@[kb "hanke2004" "(2.4), (2.5), p. 356 (over F, every p, corrected)"]
theorem eq_2_4_2_5 (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) {t : ℕ} (ht : (2 : 𝓞 F) ∈ v.asIdeal ^ t)
    (ht' : (2 : 𝓞 F) ∉ v.asIdeal ^ (t + 1)) :
    ∃ (Q' : QuadForm 𝔬 n) (P : Finset (Fin n × Fin n)) (w μ : Fin n → ℕ),
      DVR.IsJordanFormW Q' (π v) P w ∧ DVR.IsScaleExp Q' (π v) P μ ∧ DVR.IsGLEquiv (Qp v Q) Q' ∧
      (∀ k, Q.hessian.det ∈ v.asIdeal ^ k ↔ k ≤ ∑ i, DVR.detBlockExp P w μ t i) ∧
      DVR.levelExp (Qp v Q) (π v) = Finset.univ.sup (DVR.levelBlockExp P w μ t) := by
  obtain ⟨u2, hu2, h2⟩ := two_eq_pow_mul_unit v ht ht'
  obtain ⟨Q', P, w, μ, hJ, hμ, hE, ⟨u, hu, hdet⟩, hlev⟩ :=
    DVR.eq_2_4_2_5_general (Qp v Q) (nondegenerate_Qp v hQ) (irreducible_π v) (two_ne_zero' v) hu2 h2
  exact ⟨Q', P, w, μ, hJ, hμ, hE, det_mem_pow_iff v Q hu hdet, hlev⟩

/-- **(2.4) and (2.5) over $F$ where the printed values hold** ($\mathfrak p^2 \nmid 2$; Hanke 2004, p. 356): the normal
form can be taken with $\mu = w$, so $\mathrm{ord}_\mathfrak p N = \max_i \lambda''_i$ with $\lambda''_i = w_i$ on
2-dimensional blocks and $w_i + 2t$ on 1-dimensional ones (as printed), and $\mathrm{ord}_\mathfrak p \det H = \sum_i \lambda'_i$
with $\lambda'_j = 2w_j$ per 2-dimensional block (*erratum*: printed $\nu_j$) and $w_i + t$ per 1-dimensional one. -/
@[kb "hanke2004" "(2.4), (2.5), p. 356 (over F, p² ∤ 2, corrected (2.4))"]
theorem eq_2_4_2_5_of_not_sq_dvd_two (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 F) ∉ v.asIdeal ^ 2)
    {t : ℕ} (ht : (2 : 𝓞 F) ∈ v.asIdeal ^ t) (ht' : (2 : 𝓞 F) ∉ v.asIdeal ^ (t + 1)) :
    ∃ (Q' : QuadForm 𝔬 n) (P : Finset (Fin n × Fin n)) (w : Fin n → ℕ),
      DVR.IsJordanFormW Q' (π v) P w ∧ DVR.IsGLEquiv (Qp v Q) Q' ∧
      (∀ k, Q.hessian.det ∈ v.asIdeal ^ k ↔ k ≤ ∑ i, DVR.detBlockExp P w w t i) ∧
      DVR.levelExp (Qp v Q) (π v) =
        Finset.univ.sup fun i => (open Classical in if IsPaired P i then w i else w i + 2 * t) := by
  obtain ⟨u2, hu2, h2'⟩ := two_eq_pow_mul_unit v ht ht'
  have hπ2 : ¬ π v ^ 2 ∣ 2 := by rwa [π_pow_dvd_two_iff]
  obtain ⟨Q', P, w, hJ, -, hE⟩ := DVR.exists_jordanFormW_isGLEquiv (Qp v Q) (nondegenerate_Qp v hQ) (π v)
    (irreducible_π v) (two_ne_zero' v)
  obtain ⟨⟨u, hu, hdet⟩, hlev⟩ :=
    DVR.eq_2_4_2_5_of_not_sq_dvd_two hJ (irreducible_π v) hπ2 (two_ne_zero' v) hu2 h2'
  obtain ⟨s, hs, hds⟩ := hE.det_hessian
  refine ⟨Q', P, w, hJ, hE, ?_, by rw [DVR.levelExp_eq_of_isGLEquiv hE, hlev]⟩
  refine det_mem_pow_iff v Q (u := u * ((hs.unit⁻¹ : 𝔬ˣ) : 𝔬) ^ 2) (hu.mul ((Units.isUnit _).pow 2)) ?_
  have : (Qp v Q).hessian.det = ((hs.unit⁻¹ : 𝔬ˣ) : 𝔬) ^ 2 * (s ^ 2 * (Qp v Q).hessian.det) := by
    rw [← mul_assoc, ← mul_pow, IsUnit.val_inv_mul, one_pow, one_mul]
  rw [this, ← hds, hdet]; ring

/-- **(2.4) and (2.5) over $F$ verbatim at $\mathfrak p \nmid 2$** (Hanke 2004, p. 356): a diagonal normal form
$\langle \varpi^{w_i}u_i\rangle$ with $\det H \in \mathfrak p^k \iff k \le \sum_i w_i$ and $\mathrm{ord}_\mathfrak p N = \max_i w_i$. -/
@[kb "hanke2004" "(2.4), (2.5), p. 356 (over F, p ∤ 2)"]
theorem eq_2_4_2_5_nondyadic (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) :
    ∃ (Q' : QuadForm 𝔬 n) (P : Finset (Fin n × Fin n)) (w : Fin n → ℕ),
      DVR.IsJordanFormW Q' (π v) P w ∧ P = ∅ ∧ DVR.IsGLEquiv (Qp v Q) Q' ∧
      (∀ k, Q.hessian.det ∈ v.asIdeal ^ k ↔ k ≤ ∑ i, w i) ∧
      DVR.levelExp (Qp v Q) (π v) = Finset.univ.sup w := by
  have hπ2 := π_not_dvd_two v h2
  obtain ⟨Q', P, w, hJ, hP, hE⟩ := DVR.exists_jordanFormW_isGLEquiv (Qp v Q) (nondegenerate_Qp v hQ) (π v)
    (irreducible_π v) (two_ne_zero' v)
  obtain ⟨⟨u, hu, hdet⟩, hlev⟩ := DVR.eq_2_4_2_5_nondyadic_W hJ (irreducible_π v) hπ2
  obtain ⟨s, hs, hds⟩ := hE.det_hessian
  refine ⟨Q', P, w, hJ, hP hπ2, hE, ?_, by rw [DVR.levelExp_eq_of_isGLEquiv hE, hlev]⟩
  refine det_mem_pow_iff v Q (u := u * ((hs.unit⁻¹ : 𝔬ˣ) : 𝔬) ^ 2) (hu.mul ((Units.isUnit _).pow 2)) ?_
  have : (Qp v Q).hessian.det = ((hs.unit⁻¹ : 𝔬ˣ) : 𝔬) ^ 2 * (s ^ 2 * (Qp v Q).hessian.det) := by
    rw [← mul_assoc, ← mul_pow, IsUnit.val_inv_mul, one_pow, one_mul]
  rw [this, ← hds, hdet]; ring

end QuadFormsKB.LocalDensity.NF

end
