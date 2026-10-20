/-
# Hilbert modular forms VII: the Koecher principle, boundedness form

`Koecher.lean` proves the coefficient form of Koecher's principle: for $d = [F:\mathbb{Q}] \ge 2$ the Fourier coefficients
$a_\nu$ of a holomorphic $f$ invariant under $T(I)$ and $\mathrm{diag}(u^m, u^{-m})$ vanish unless $\nu = 0$ or $\nu \gg 0$. With
Fourier inversion (`FourierInversion.lean`) this gives the **boundedness form**:

* `norm_le_of_qCoeff_nonneg` (any $\iota$, any lattice): if $a_\nu \ne 0$ only for $\nu \ge 0$ (componentwise), then $f$ is
  bounded on $\{\operatorname{Im}z_v \ge c\ \forall v\}$ for every $c > 0$, by
  $\sum_\nu|a_\nu|e^{-2\pi c\sum_v\nu_v} < \infty$.
* `koecher_bounded`, `koecher_isBoundedAtImInftyPi` ($F$ totally real, $d \ge 2$): $f$ is bounded at the cusp $\infty$, with
  **no hypothesis at the cusps**.
* `koecher_slash_isBoundedAtImInftyPi`, `mem_modularFormSpace_of_koecher`: **all cusps.** If for every
  $\gamma \in \mathrm{SL}_2(F)$ the conjugate $\gamma^{-1}\Gamma\gamma$ contains the translations by some fractional ideal
  $I_\gamma$ and $\mathrm{diag}(u^{m_\gamma}, u^{-m_\gamma})$ for all units $u$ (some $m_\gamma \ge 1$), then every holomorphic
  $\Gamma$-invariant $f$ lies in $M_k(\Gamma)$: condition (iii) of `modularFormSpace` is automatic for $d \ge 2$. (The
  group-theoretic hypothesis is verified in `KoecherCusps.lean` for every $\Gamma \supseteq \Gamma(\mathfrak N)$, $\mathfrak N \ne 0$.)
* `dualVec_koecherBasis`: the dual lattice of the real image of $I$ is the image of the trace dual $I^\vee$
  (`QuadFormsKB.Analysis.dualElt`), so $\langle\nu_n, z\rangle = \operatorname{Tr}(\nu z)$ with $\nu \in I^\vee$.

Sources: Freitag, *Hilbert Modular Forms* (1990), Ch. I §4 (Koecher principle) [unverified]; Garrett, *Holomorphic Hilbert
Modular Forms* (1990), Ch. 1 [unverified].
-/
import QuadFormsKB.HilbertModular.Koecher
import QuadFormsKB.HilbertModular.FourierInversion

open Matrix NumberField NumberField.InfinitePlace UpperHalfPlane Complex Filter
open scoped MatrixGroups Real nonZeroDivisors ModularForm

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

section General

variable {ι : Type*} [Fintype ι] {J : Type*} [Fintype J]

/-- **Boundedness from nonnegative support.** If $f$ is holomorphic and $\Lambda$-periodic and $a_{\nu_n} \ne 0$ only when
$\nu_n \ge 0$ componentwise, then for every $c > 0$, $f$ is bounded on $\{z : \operatorname{Im}z_v \ge c\ \forall v\}$. -/
theorem norm_le_of_qCoeff_nonneg [DecidableEq ι] {f : (ι → ℍ) → ℂ} {b : Module.Basis J ℝ (ι → ℝ)}
    (hf : IsHolomorphic f) (hper : IsLatticePeriodic f b)
    (hsupp : ∀ n, qCoeff f b (dualVec b n) ≠ 0 → ∀ v, 0 ≤ dualVec b n v) {c : ℝ} (hc : 0 < c) :
    ∃ M, ∀ z : ι → ℍ, (∀ v, c ≤ (z v).im) → ‖f z‖ ≤ M := by
  set z₀ : ι → ℍ := ptXY 0 (fun _ => c)
  have hz₀ : imVec z₀ = fun _ => c := imVec_ptXY fun _ => hc
  refine ⟨∑' n, ‖qCoeff f b (dualVec b n) * qTerm (dualVec b n) z₀‖, fun z hz => ?_⟩
  rw [← (hasSum_qExpansion hf hper z).tsum_eq]
  refine (norm_tsum_le_tsum_norm (summable_norm_qExpansion hf hper z)).trans
    ((summable_norm_qExpansion hf hper z).tsum_le_tsum (fun n => ?_)
      (summable_norm_qExpansion hf hper z₀))
  rw [norm_mul, norm_mul, norm_qTerm, norm_qTerm, hz₀]
  by_cases h0 : qCoeff f b (dualVec b n) = 0
  · simp [h0]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  have : pair (dualVec b n) (fun _ => c) ≤ pair (dualVec b n) (imVec z) :=
    Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (hz v) (hsupp n h0 v)
  nlinarith [Real.pi_pos]

/-- Eventually (along `atImInftyPi`) $\operatorname{Im}z_v \ge c$ for all $v$. -/
lemma eventually_im_ge (c : ℝ) : ∀ᶠ z in (atImInftyPi : Filter (ι → ℍ)), ∀ v, c ≤ (z v).im :=
  eventually_all.mpr fun v => mem_iInf_of_mem v (tendsto_comap.eventually (eventually_ge_atTop c))

lemma isBoundedAtImInftyPi_of_bound {f : (ι → ℍ) → ℂ} {c M : ℝ}
    (h : ∀ z : ι → ℍ, (∀ v, c ≤ (z v).im) → ‖f z‖ ≤ M) : IsBoundedAtImInftyPi f := by
  refine Asymptotics.IsBigO.of_bound M ((eventually_im_ge c).mono fun z hz => ?_)
  simpa using h z hz

end General

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/-! ### The dual lattice of a fractional ideal -/

lemma latElt_surj (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) {β : F}
    (hβ : β ∈ (I : FractionalIdeal (𝓞 F)⁰ F)) : ∃ m, QuadFormsKB.Analysis.latElt I m = β := by
  refine ⟨(QuadFormsKB.Analysis.latEquiv I).symm ⟨β, hβ⟩, ?_⟩
  rw [← QuadFormsKB.Analysis.latEquiv_coe, Equiv.apply_symm_apply]

/-- $\operatorname{Tr}(\nu_m^\vee\beta) \in \mathbb{Z}$ for $\beta \in I$: `dualElt I m` lies in the trace dual $I^\vee$. -/
lemma trace_dualElt_mul_mem (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (m : Fin (Module.finrank ℚ F) → ℤ)
    {β : F} (hβ : β ∈ (I : FractionalIdeal (𝓞 F)⁰ F)) :
    ∃ n : ℤ, Algebra.trace ℚ F (QuadFormsKB.Analysis.dualElt I m * β) = n := by
  obtain ⟨k, rfl⟩ := latElt_surj I hβ
  refine ⟨∑ j, k j * m j, ?_⟩
  rw [QuadFormsKB.Analysis.latElt, Finset.mul_sum, map_sum]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_left_comm, show (k j : F) = algebraMap ℚ F (k j) by simp, ← Algebra.smul_def, map_smul,
    mul_comm, QuadFormsKB.Analysis.trace_bq_mul_dualElt, smul_eq_mul]

/-- **The dual lattice of $I$ is the trace dual**: $\nu_m$ (`dualVec`) for the lattice basis of $I$ is the real image of
$\sum_jm_jb_j^\vee \in I^\vee$ (`QuadFormsKB.Analysis.dualElt`). -/
lemma dualVec_koecherBasis (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (m : Fin (Module.finrank ℚ F) → ℤ) :
    dualVec (koecherBasis I) m = realVec (QuadFormsKB.Analysis.dualElt I m) := by
  refine (pairEquiv (koecherBasis I)).symm_apply_eq.mpr ?_
  funext j
  change (m j : ℝ) = pair _ (koecherBasis I j)
  rw [koecherBasis_apply, pair_realVec, mul_comm, QuadFormsKB.Analysis.trace_bq_mul_dualElt]
  simp

/-! ### Boundedness at $\infty$ -/

/-- Under the hypotheses of `koecher`, the $q$-coefficients for the lattice $I$ vanish unless $\nu_n \ge 0$. -/
lemma koecher_qCoeff_nonneg (hd : 2 ≤ Fintype.card (InfinitePlace F)) {Γ : Subgroup SL(2, F)} {k : ℤ}
    {f : (InfinitePlace F → ℍ) → ℂ} (hinv : ∀ γ ∈ Γ, f ∣[k] slHom (realEmb F) γ = f)
    (hf : IsHolomorphic f) (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (hT : ∀ β ∈ (I : FractionalIdeal (𝓞 F)⁰ F), transl β ∈ Γ) {m : ℕ} (hm : 0 < m)
    (hU : ∀ u : (𝓞 F)ˣ, diagU (unitF u ^ m) ∈ Γ) (n : Fin (Module.finrank ℚ F) → ℤ)
    (hn : qCoeff f (koecherBasis I) (dualVec (koecherBasis I) n) ≠ 0) :
    ∀ v, 0 ≤ dualVec (koecherBasis I) n v := by
  intro w
  by_contra hw
  rw [not_le] at hw
  rw [dualVec_koecherBasis] at hw hn
  apply hn
  have h0 := koecher hd hinv hf I hT hm hU (fun β hβ => trace_dualElt_mul_mem I n hβ) hw
    (y := 1) (fun _ => one_pos)
  rw [qCoeff, h0, zero_mul]

/-- **The Koecher principle, boundedness form** ($d \ge 2$). Let $f$ be holomorphic on $\mathbb{H}^d$ with $f\,|_k\,\gamma = f$
for $\gamma \in \Gamma$, where $\Gamma \ni T(\beta)$ ($\beta \in I$, a fractional ideal) and $\Gamma \ni \mathrm{diag}(u^m, u^{-m})$ for all
units $u$ ($m \ge 1$). Then for every $c > 0$, $f$ is bounded on $\{z : \operatorname{Im}z_v \ge c\ \forall v\}$. No condition
at the cusps is assumed.

Parameters: as in `koecher`; `c`, `hc` ($c > 0$). -/
@[kb "freitag1990" "Ch. I, §4, Koecher principle [unverified]"]
theorem koecher_bounded (hd : 2 ≤ Fintype.card (InfinitePlace F)) {Γ : Subgroup SL(2, F)} {k : ℤ}
    {f : (InfinitePlace F → ℍ) → ℂ} (hinv : ∀ γ ∈ Γ, f ∣[k] slHom (realEmb F) γ = f)
    (hf : IsHolomorphic f) (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (hT : ∀ β ∈ (I : FractionalIdeal (𝓞 F)⁰ F), transl β ∈ Γ) {m : ℕ} (hm : 0 < m)
    (hU : ∀ u : (𝓞 F)ˣ, diagU (unitF u ^ m) ∈ Γ) {c : ℝ} (hc : 0 < c) :
    ∃ M, ∀ z : InfinitePlace F → ℍ, (∀ v, c ≤ (z v).im) → ‖f z‖ ≤ M := by
  classical
  exact norm_le_of_qCoeff_nonneg hf (isLatticePeriodic_of_transl hinv I hT)
    (koecher_qCoeff_nonneg hd hinv hf I hT hm hU) hc

/-- **Koecher: bounded at $i\infty$** ($d \ge 2$), under the hypotheses of `koecher_bounded`. -/
theorem koecher_isBoundedAtImInftyPi (hd : 2 ≤ Fintype.card (InfinitePlace F))
    {Γ : Subgroup SL(2, F)} {k : ℤ} {f : (InfinitePlace F → ℍ) → ℂ}
    (hinv : ∀ γ ∈ Γ, f ∣[k] slHom (realEmb F) γ = f) (hf : IsHolomorphic f)
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (hT : ∀ β ∈ (I : FractionalIdeal (𝓞 F)⁰ F), transl β ∈ Γ)
    {m : ℕ} (hm : 0 < m) (hU : ∀ u : (𝓞 F)ˣ, diagU (unitF u ^ m) ∈ Γ) :
    IsBoundedAtImInftyPi f := by
  obtain ⟨M, hM⟩ := koecher_bounded hd hinv hf I hT hm hU one_pos
  exact isBoundedAtImInftyPi_of_bound hM

/-! ### All cusps -/

/-- If $f$ is $\Gamma$-invariant and $\gamma\delta\gamma^{-1} \in \Gamma$, then $f\,|_k\,\gamma$ is invariant under $\delta$. -/
lemma slash_conj_invariant {Γ : Subgroup SL(2, F)} {k : ℤ} {f : (InfinitePlace F → ℍ) → ℂ}
    (hinv : ∀ γ ∈ Γ, f ∣[k] slHom (realEmb F) γ = f) (γ δ : SL(2, F)) (h : γ * δ * γ⁻¹ ∈ Γ) :
    (f ∣[k] slHom (realEmb F) γ) ∣[k] slHom (realEmb F) δ = f ∣[k] slHom (realEmb F) γ := by
  rw [← SlashAction.slash_mul, ← map_mul,
    show γ * δ = (γ * δ * γ⁻¹) * γ by group, map_mul, SlashAction.slash_mul, hinv _ h]

/-- **Koecher at the cusp $\gamma\infty$** ($d \ge 2$): if $\gamma^{-1}\Gamma\gamma$ contains $T(I_\gamma)$ and
$\mathrm{diag}(u^m, u^{-m})$ for all units, then $f\,|_k\,\gamma$ is bounded at $i\infty$. -/
theorem koecher_slash_isBoundedAtImInftyPi (hd : 2 ≤ Fintype.card (InfinitePlace F))
    {Γ : Subgroup SL(2, F)} {k : ℤ} {f : (InfinitePlace F → ℍ) → ℂ}
    (hinv : ∀ γ ∈ Γ, f ∣[k] slHom (realEmb F) γ = f) (hf : IsHolomorphic f) (γ : SL(2, F))
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (hT : ∀ β ∈ (I : FractionalIdeal (𝓞 F)⁰ F), γ * transl β * γ⁻¹ ∈ Γ) {m : ℕ} (hm : 0 < m)
    (hU : ∀ u : (𝓞 F)ˣ, γ * diagU (unitF u ^ m) * γ⁻¹ ∈ Γ) :
    IsBoundedAtImInftyPi (f ∣[k] slHom (realEmb F) γ) := by
  set Γ' : Subgroup SL(2, F) := Γ.comap (MulAut.conj γ).toMonoidHom
  have hmem : ∀ δ, δ ∈ Γ' ↔ γ * δ * γ⁻¹ ∈ Γ := fun δ => Iff.rfl
  exact koecher_isBoundedAtImInftyPi hd (Γ := Γ')
    (fun δ hδ => slash_conj_invariant hinv γ δ ((hmem δ).mp hδ)) (hf.slash k _) I
    (fun β hβ => (hmem _).mpr (hT β hβ)) hm (fun u => (hmem _).mpr (hU u))

/-- **The cusp condition is automatic for $d \ge 2$.** If every conjugate $\gamma^{-1}\Gamma\gamma$ ($\gamma \in \mathrm{SL}_2(F)$)
contains the translations by some fractional ideal and $\mathrm{diag}(u^m, u^{-m})$ for all units (some $m \ge 1$), then every
holomorphic $f$ with $f\,|_k\,\gamma = f$ ($\gamma \in \Gamma$) is in $M_k(\Gamma)$ (`modularFormSpace`). -/
@[kb "freitag1990" "Ch. I, §4, Koecher principle [unverified]"]
theorem mem_modularFormSpace_of_koecher (hd : 2 ≤ Fintype.card (InfinitePlace F))
    {Γ : Subgroup SL(2, F)} {k : ℤ} {f : (InfinitePlace F → ℍ) → ℂ}
    (hinv : ∀ γ ∈ Γ, f ∣[k] slHom (realEmb F) γ = f) (hf : IsHolomorphic f)
    (hcusp : ∀ γ : SL(2, F), ∃ I : (FractionalIdeal (𝓞 F)⁰ F)ˣ, ∃ m : ℕ, 0 < m ∧
      (∀ β ∈ (I : FractionalIdeal (𝓞 F)⁰ F), γ * transl β * γ⁻¹ ∈ Γ) ∧
      ∀ u : (𝓞 F)ˣ, γ * diagU (unitF u ^ m) * γ⁻¹ ∈ Γ) :
    f ∈ modularFormSpace (realEmb F) Γ k := by
  refine ⟨hinv, hf, fun γ => ?_⟩
  obtain ⟨I, m, hm, hT, hU⟩ := hcusp γ
  exact koecher_slash_isBoundedAtImInftyPi hd hinv hf γ I hT hm hU

end QuadFormsKB.HilbertModular
