import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Binary.RelNormDisc
import QuadFormsKB.Siegel.NFGoodPrime

/-!
# Local densities of the norm form over $F$ at the good primes

Let $E/F$ be a quadratic extension of number fields, $\theta \in \mathcal O_E$ with $\sigma(\theta) = -\theta$ and $\delta = \theta^2 \in \mathcal O_F$.

* **The splitting character by a residue symbol** (`relChar_eq_charNF`): at a prime $\mathfrak p \nmid 2\delta$ of $F$, $\mathfrak p$ is unramified
  in $E$ and $\chi_{E/F}(\mathfrak p) = \left(\frac{\delta}{\mathfrak p}\right)$ (the `relChar`, defined by the splitting of $\mathfrak p$). Proof, from
  the splitting law only: if $\mathfrak P \mid \mathfrak p$ has residue degree $1$ then
  $\theta \equiv c \pmod{\mathfrak P}$ with $c \in \mathcal O_F$, so $\delta \equiv c^2$; conversely if
  $\delta \equiv c^2$ and $\sigma(\mathfrak P) = \mathfrak P$ (inert or ramified), then $\theta \equiv \pm c$ and
  applying $\sigma$ gives $2c \in \mathfrak P$, so $\delta \in \mathfrak p$.
* **Binary densities at a non-dyadic unimodular prime** (`DVR.localDensity_binary_diag`): for a unit diagonal form $\langle a_0, a_1\rangle$ over a
  DVR with $\pi \nmid 2$ and $m = \pi^v u \ne 0$, $\beta_\pi(m) = (1 - \chi/q)\sum_{j=0}^{v}\chi^j$, $\chi = \left(\frac{-a_0a_1}{\pi}\right)$. Proof:
  Table 1 (`card_diag_mod_pi`) at $v \le 1$ and the Zero-type step of (5.7) (`localDensity_pow_sq_step`), which for $n = 2$ needs no
  isotropy.
* **The norm form at the good primes** (`localDensity_normFormBasis_good`): for $\mathcal O_E$ free over $\mathcal O_F$ with basis $b$, $Q_b$ its norm form
  (`normFormBasis`), and $\mathfrak p \nmid 2\Delta_{E/F}(b)$ (i.e. `IsGoodPrimeNF`), for every $\nu \ne 0$:
  $$\beta_\mathfrak p(Q_b, \nu) = \Big(1 - \frac{\chi_{E/F}(\mathfrak p)}{N\mathfrak p}\Big)\sum_{j=0}^{v_\mathfrak p(\nu)}\chi_{E/F}(\mathfrak p)^j,$$
  the analogue over $F$ of `localDensity_good_binary`. With the ideal count `relNormCount_eq_finprod` this is the
  local factor of $\#\{\mathfrak B : N\mathfrak B = (\nu)\}$ times the Euler factor $(1 - \chi(\mathfrak p)/N\mathfrak p)$ of $L(1,\chi_{E/F})^{-1}$.

Sources: Hanke 2004, Table 1 (p. 363), (5.7) (p. 369); Siegel (1935) [unverified locator]; Neukirch Ch. I §8 [unverified].
-/

open NumberField Module IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Binary.Rel

/-! ### $\chi_{E/F}(\mathfrak p) = (\delta/\mathfrak p)$ at $\mathfrak p \nmid 2\delta$ -/

section RelChar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

theorem algebraMap_mem_iff {𝔭 : HeightOneSpectrum (𝓞 F)} {P : Ideal (𝓞 E)} [P.LiesOver 𝔭.asIdeal] (x : 𝓞 F) :
    algebraMap (𝓞 F) (𝓞 E) x ∈ P ↔ x ∈ 𝔭.asIdeal := by
  rw [Ideal.LiesOver.over (P := P) (p := 𝔭.asIdeal), Ideal.under, Ideal.mem_comap]

/-- If $\sigma(\mathfrak P) = \mathfrak P$, $\mathfrak p \nmid 2$ and $\theta \equiv c \pmod{\mathfrak P}$ ($c \in \mathcal O_F$), then $\delta = \theta^2 \in \mathfrak p$. -/
theorem mem_of_conj_stable {𝔭 : HeightOneSpectrum (𝓞 F)} {θ : 𝓞 E} (hθ : conjO F E θ = -θ) {δ : 𝓞 F}
    (hδ : algebraMap (𝓞 F) (𝓞 E) δ = θ ^ 2) {P : Ideal (𝓞 E)} [P.IsPrime] [P.LiesOver 𝔭.asIdeal]
    (hσ : conjIdeal F P = P) (h2 : (2 : 𝓞 F) ∉ 𝔭.asIdeal) {c : 𝓞 F}
    (hc : θ - algebraMap (𝓞 F) (𝓞 E) c ∈ P) : δ ∈ 𝔭.asIdeal := by
  have hc' : conjO F E (θ - algebraMap (𝓞 F) (𝓞 E) c) ∈ P := by
    rw [← hσ]; exact Ideal.mem_map_of_mem _ hc
  rw [map_sub, hθ, conjO_algebraMap] at hc'
  have h2c : algebraMap (𝓞 F) (𝓞 E) (2 * c) ∈ P := by
    have := P.add_mem hc hc'
    rw [show θ - algebraMap (𝓞 F) (𝓞 E) c + (-θ - algebraMap (𝓞 F) (𝓞 E) c) =
      -algebraMap (𝓞 F) (𝓞 E) (2 * c) by rw [map_mul, map_ofNat]; ring] at this
    exact neg_mem_iff.mp this
  rw [algebraMap_mem_iff (𝔭 := 𝔭) (P := P)] at h2c
  have hcp : c ∈ 𝔭.asIdeal := (𝔭.isPrime.mem_or_mem h2c).resolve_left h2
  have hθP : θ ∈ P := by
    have := P.add_mem hc ((algebraMap_mem_iff (P := P) c).mpr hcp)
    simpa using this
  rw [← algebraMap_mem_iff (P := P), hδ, pow_two]
  exact P.mul_mem_left _ hθP

theorem isMaximal_of_primesOver {𝔭 : HeightOneSpectrum (𝓞 F)} (P : 𝔭.asIdeal.primesOver (𝓞 E)) :
    P.1.IsMaximal := by
  have hP := P.2
  have : P.1.IsPrime := hP.1
  have : P.1.LiesOver 𝔭.asIdeal := hP.2
  exact Ideal.IsPrime.isMaximal hP.1 (by
    intro h0
    have := Ideal.LiesOver.over (P := P.1) (p := 𝔭.asIdeal)
    rw [h0] at this
    apply 𝔭.ne_bot
    rw [this]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E)))

/-- **$\chi_{E/F}(\mathfrak p) = (\delta/\mathfrak p)$ at $\mathfrak p \nmid 2\delta$:** for $\theta \in \mathcal O_E$ with $\sigma\theta = -\theta$ and $\delta = \theta^2 \in \mathcal O_F$,
$\mathfrak p \nmid 2\delta$ is unramified, and it splits iff $\delta$ is a square modulo $\mathfrak p$. -/
@[kb "neukirch1999" "Ch. I §8, Prop. 8.3 [unverified]"]
theorem relChar_eq_one_iff_sq {θ : 𝓞 E} (hθ : conjO F E θ = -θ) {δ : 𝓞 F}
    (hδ : algebraMap (𝓞 F) (𝓞 E) δ = θ ^ 2) {𝔭 : HeightOneSpectrum (𝓞 F)} (h2 : (2 : 𝓞 F) ∉ 𝔭.asIdeal)
    (hδ𝔭 : δ ∉ 𝔭.asIdeal) :
    relChar E 𝔭 ≠ 0 ∧ (relChar E 𝔭 = 1 ↔ ∃ c : 𝓞 F, δ - c ^ 2 ∈ 𝔭.asIdeal) := by
  have : 𝔭.asIdeal.IsMaximal := 𝔭.isMaximal
  rcases splitting (Algebra.IsQuadraticExtension.finrank_eq_two F E) 𝔭 with
    ⟨h, P₀, -, -, -, -, hf, -, -⟩ | ⟨h, P₀, hall, -, -⟩ | ⟨h, P₀, hall, -, hf⟩
  · -- split
    refine ⟨by rw [h]; norm_num, fun _ => ?_, fun _ => h⟩
    have : P₀.1.IsPrime := P₀.2.1
    have : P₀.1.LiesOver 𝔭.asIdeal := P₀.2.2
    have : P₀.1.IsMaximal := isMaximal_of_primesOver P₀
    obtain ⟨c, hc⟩ := exists_sub_mem_of_inertiaDeg_one 𝔭.asIdeal P₀.1 hf θ
    refine ⟨c, ?_⟩
    rw [← algebraMap_mem_iff (P := P₀.1), map_sub, hδ, map_pow,
      show θ ^ 2 - algebraMap (𝓞 F) (𝓞 E) c ^ 2 =
        (θ - algebraMap (𝓞 F) (𝓞 E) c) * (θ + algebraMap (𝓞 F) (𝓞 E) c) by ring]
    exact P₀.1.mul_mem_right _ hc
  · -- inert
    have : P₀.1.IsPrime := P₀.2.1
    have : P₀.1.LiesOver 𝔭.asIdeal := P₀.2.2
    have hσ : conjIdeal F P₀.1 = P₀.1 :=
      congrArg Subtype.val (hall ⟨conjIdeal F P₀.1, conjIdeal_mem_primesOver 𝔭.asIdeal P₀⟩)
    refine ⟨by rw [h]; norm_num, fun h1 => by rw [h] at h1; norm_num at h1, fun ⟨c, hc⟩ => ?_⟩
    exfalso
    have hc' : (θ - algebraMap (𝓞 F) (𝓞 E) c) * (θ + algebraMap (𝓞 F) (𝓞 E) c) ∈ P₀.1 := by
      rw [show (θ - algebraMap (𝓞 F) (𝓞 E) c) * (θ + algebraMap (𝓞 F) (𝓞 E) c) =
        algebraMap (𝓞 F) (𝓞 E) (δ - c ^ 2) by rw [map_sub, hδ, map_pow]; ring, algebraMap_mem_iff (𝔭 := 𝔭) (P := P₀.1)]
      exact hc
    rcases P₀.2.1.mem_or_mem hc' with h1 | h1
    · exact hδ𝔭 (mem_of_conj_stable hθ hδ hσ h2 h1)
    · exact hδ𝔭 (mem_of_conj_stable (c := -c) hθ hδ hσ h2 (by rwa [map_neg, sub_neg_eq_add]))
  · -- ramified: impossible
    exfalso
    have : P₀.1.IsPrime := P₀.2.1
    have : P₀.1.LiesOver 𝔭.asIdeal := P₀.2.2
    have : P₀.1.IsMaximal := isMaximal_of_primesOver P₀
    have hσ : conjIdeal F P₀.1 = P₀.1 :=
      congrArg Subtype.val (hall ⟨conjIdeal F P₀.1, conjIdeal_mem_primesOver 𝔭.asIdeal P₀⟩)
    obtain ⟨c, hc⟩ := exists_sub_mem_of_inertiaDeg_one 𝔭.asIdeal P₀.1 hf θ
    exact hδ𝔭 (mem_of_conj_stable hθ hδ hσ h2 hc)

end RelChar

/-! ### $\chi_{E/F}(\mathfrak p)$ as the residue symbol `Siegel.charNF` -/

section CharNF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

theorem residue_ι_surjective (v : HeightOneSpectrum (𝓞 F)) (y : IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :
    ∃ c : 𝓞 F, IsLocalRing.residue _ (LocalDensity.NF.ι v c) = y := by
  obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨c, hc⟩ := LocalDensity.NF.redHom_surjective v 1 (Ideal.Quotient.mk _ z)
  refine ⟨c, ?_⟩
  rw [LocalDensity.NF.redHom, RingHom.comp_apply, Ideal.Quotient.eq, Ideal.mem_span_singleton, pow_one] at hc
  rw [← sub_eq_zero, ← map_sub]
  exact (LocalDensity.DVR.residue_eq_zero_iff_dvd (LocalDensity.NF.irreducible_π v) _).2 hc

theorem charNF_eq_one_iff (v : HeightOneSpectrum (𝓞 F)) {δ : 𝓞 F} (hδ : δ ∉ v.asIdeal) :
    Siegel.charNF v δ = 1 ↔ ∃ c : 𝓞 F, δ - c ^ 2 ∈ v.asIdeal := by
  have hne : IsLocalRing.residue _ (LocalDensity.NF.ι v δ) ≠ 0 := by
    rw [Ne, LocalDensity.DVR.residue_eq_zero_iff_dvd (LocalDensity.NF.irreducible_π v),
      LocalDensity.NF.π_dvd_ι_iff]
    exact hδ
  rw [Siegel.charNF, quadraticChar_one_iff_isSquare hne]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨c, rfl⟩ := residue_ι_surjective v y
    refine ⟨c, ?_⟩
    rw [← LocalDensity.NF.π_dvd_ι_iff, ← LocalDensity.DVR.residue_eq_zero_iff_dvd (LocalDensity.NF.irreducible_π v),
      map_sub, map_sub, map_pow, map_pow, hy]
    ring
  · rintro ⟨c, hc⟩
    refine ⟨IsLocalRing.residue _ (LocalDensity.NF.ι v c), ?_⟩
    rw [← LocalDensity.NF.π_dvd_ι_iff, ← LocalDensity.DVR.residue_eq_zero_iff_dvd (LocalDensity.NF.irreducible_π v),
      map_sub, map_sub, map_pow, map_pow, sub_eq_zero] at hc
    rw [hc]; ring

theorem relChar_trichotomy (𝔭 : HeightOneSpectrum (𝓞 F)) :
    relChar E 𝔭 = 1 ∨ relChar E 𝔭 = -1 ∨ relChar E 𝔭 = 0 := by
  rcases splitting (Algebra.IsQuadraticExtension.finrank_eq_two F E) 𝔭 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- **$\chi_{E/F}(\mathfrak p) = \left(\frac{\delta}{\mathfrak p}\right)$** (the residue symbol `Siegel.charNF`) at $\mathfrak p \nmid 2\delta$, for $\delta = \theta^2$,
$\sigma\theta = -\theta$. -/
@[kb "neukirch1999" "Ch. I §8, Prop. 8.3 [unverified]"]
theorem relChar_eq_charNF {θ : 𝓞 E} (hθ : conjO F E θ = -θ) {δ : 𝓞 F}
    (hδ : algebraMap (𝓞 F) (𝓞 E) δ = θ ^ 2) {𝔭 : HeightOneSpectrum (𝓞 F)} (h2 : (2 : 𝓞 F) ∉ 𝔭.asIdeal)
    (hδ𝔭 : δ ∉ 𝔭.asIdeal) : relChar E 𝔭 = Siegel.charNF 𝔭 δ := by
  obtain ⟨h0, hiff⟩ := relChar_eq_one_iff_sq hθ hδ h2 hδ𝔭
  have hne : IsLocalRing.residue _ (LocalDensity.NF.ι 𝔭 δ) ≠ 0 := by
    rw [Ne, LocalDensity.DVR.residue_eq_zero_iff_dvd (LocalDensity.NF.irreducible_π 𝔭),
      LocalDensity.NF.π_dvd_ι_iff]
    exact hδ𝔭
  by_cases hsq : ∃ c : 𝓞 F, δ - c ^ 2 ∈ 𝔭.asIdeal
  · rw [hiff.mpr hsq, (charNF_eq_one_iff 𝔭 hδ𝔭).mpr hsq]
  · have h1 : relChar E 𝔭 = -1 := by
      rcases relChar_trichotomy (E := E) 𝔭 with h | h | h
      · exact absurd (hiff.mp h) hsq
      · exact h
      · exact absurd h h0
    rw [h1]
    have hc := (charNF_eq_one_iff 𝔭 hδ𝔭).not.mpr hsq
    rw [Siegel.charNF] at hc ⊢
    rcases quadraticChar_dichotomy hne with h | h
    · exact absurd h hc
    · exact h.symm

end CharNF

end QuadFormsKB.Binary.Rel

/-! ### Binary densities over a DVR at a non-dyadic unimodular prime -/

namespace QuadFormsKB.LocalDensity.DVR

open QuadForm

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

variable [Fintype (IsLocalRing.ResidueField R)] [DecidableEq (IsLocalRing.ResidueField R)]

/-- $\chi = \left(\frac{-a_0a_1}{\pi}\right)$ for a binary unit diagonal form. -/
def binChi (a : Fin 2 → R) : ℤ := quadraticChar (IsLocalRing.ResidueField R) (IsLocalRing.residue R (-(a 0 * a 1)))

theorem binChi_sq {a : Fin 2 → R} {π : R} (hπ : Irreducible π) (ha : ∀ i, ¬ π ∣ a i) : binChi a ^ 2 = 1 := by
  rw [binChi]
  refine quadraticChar_sq_one fun h => ?_
  rw [residue_eq_zero_iff_dvd hπ, dvd_neg] at h
  rcases hπ.prime.dvd_or_dvd h with h | h
  · exact ha 0 h
  · exact ha 1 h

theorem repCount_one_binary {a : Fin 2 → R} {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2) (ha : ∀ i, ¬ π ∣ a i) :
    (repCount (QuadForm.diag a) π 1 0 : ℤ) = q R + binChi a * (q R - 1) ∧
      ∀ u : R, ¬ π ∣ u → (repCount (QuadForm.diag a) π 1 u : ℤ) = q R - binChi a := by
  have hdiag := fun u hu => (card_diag_mod_pi a π hπ h2 ha (by norm_num) u hu).1 even_two
  have e : ((-1 : R) ^ (2 / 2) * ∏ i, a i) = -(a 0 * a 1) := by
    rw [Fin.prod_univ_two]; norm_num
  refine ⟨?_, fun u hu => ?_⟩
  · obtain ⟨h0, -⟩ := hdiag 1 (fun h => hπ.not_isUnit (isUnit_of_dvd_one h))
    rw [h0, e]; norm_num [binChi]
  · obtain ⟨-, h1⟩ := hdiag u hu
    rw [h1, e]; norm_num [binChi]

/-- $\beta_\pi(u) = 1 - \chi/q$ at a unit $u$. -/
theorem localDensity_binary_unit {a : Fin 2 → R} {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2) (ha : ∀ i, ¬ π ∣ a i)
    (u : R) (hu : ¬ π ∣ u) :
    localDensity (QuadForm.diag a) π u = 1 - (binChi a : ℝ) / (q R : ℝ) := by
  have hq : (0 : ℝ) < q R := by exact_mod_cast q_pos (R := R)
  rw [localDensity_unit a π hπ h2 ha u hu]
  have := (repCount_one_binary hπ h2 ha).2 u hu
  have h' : (repCount (QuadForm.diag a) π 1 u : ℝ) = q R - binChi a := by exact_mod_cast this
  rw [h']
  field_simp
  ring

/-- $K_0 = \beta^{\mathrm{Good}\cup\mathrm{Bad}}_\pi(\pi^2T) = (1+\chi)(1 - 1/q)$. -/
theorem localDensityOf_binary_K0 {a : Fin 2 → R} {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2) (ha : ∀ i, ¬ π ∣ a i)
    (T : R) :
    localDensityOf (QuadForm.diag a) π (π ^ 2 * T) (fun k x => ¬ IsZeroType π k x) =
      (1 + binChi a) * (1 - 1 / (q R : ℝ)) := by
  have hq : (0 : ℝ) < q R := by exact_mod_cast q_pos (R := R)
  rw [localDensityOf_nonZero_diag_sq a π hπ h2 ha T]
  have := (repCount_one_binary hπ h2 ha).1
  have h' : (repCount (QuadForm.diag a) π 1 0 : ℝ) = q R + binChi a * (q R - 1) := by exact_mod_cast this
  rw [h']
  field_simp
  norm_num
  ring

/-- **The Zero-type step for $n = 2$:** $\beta_\pi(\pi^{2e}T) = eK_0 + \beta_\pi(T)$ ($T \ne 0$). For $n = 2$ the factor $q^{-(n-2)}$ is $1$ and
no isotropy is needed. *Update (Hanke 2004, (5.7)):* (5.7) is stated for isotropic $Q$, but holds for every nondegenerate $Q$
with $n \ge 2$ (isotropy is used only to exclude $n = 1$). -/
theorem localDensity_binary_pow_sq {a : Fin 2 → R} {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2) (ha : ∀ i, ¬ π ∣ a i)
    (hQ : (QuadForm.diag a).Nondegenerate) (T : R) (hT0 : T ≠ 0) (e : ℕ) :
    localDensity (QuadForm.diag a) π (π ^ (2 * e) * T) =
      e * ((1 + binChi a) * (1 - 1 / (q R : ℝ))) + localDensity (QuadForm.diag a) π T := by
  have h20 : (2 : R) ≠ 0 := fun h => h2 (h ▸ dvd_zero _)
  have hq0 : (q R : ℝ) ≠ 0 := by exact_mod_cast (q_pos (R := R)).ne'
  have hstab : ∀ᶠ k in Filter.atTop, ∀ ν ≥ 1,
      repCountOf (QuadForm.diag a) π k (π ^ (2 * ν) * T) (fun x => ¬ IsZeroType π k x) =
        repCountOf (QuadForm.diag a) π k (π ^ 2 * T) (fun x => ¬ IsZeroType π k x) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk ν hν
    have h1 := normalized_nonZero_diag a π hπ h2 ha (π ^ (2 * ν) * T) k hk
    have h1' := normalized_nonZero_diag a π hπ h2 ha (π ^ 2 * T) k hk
    have hc : repCountOf (QuadForm.diag a) π 1 (π ^ (2 * ν) * T) (fun x => ¬ IsZeroType π 1 x) =
        repCountOf (QuadForm.diag a) π 1 (π ^ 2 * T) (fun x => ¬ IsZeroType π 1 x) := by
      rw [repCountOf_congr _ π 1 (m' := 0) ((mk_pow_one_eq_zero_iff π _).2
          (Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) _)),
        repCountOf_congr _ π 1 (m := π ^ 2 * T) (m' := 0) ((mk_pow_one_eq_zero_iff π _).2
          (Dvd.dvd.mul_right (dvd_pow_self _ two_ne_zero) _))]
    rw [hc, ← h1'] at h1
    have hpow : (q R : ℝ) ^ (k * (2 - 1)) ≠ 0 := pow_ne_zero _ hq0
    exact_mod_cast (div_left_inj' hpow).mp h1
  have hK := localDensityOf_nonZero_eq (QuadForm.diag a) hQ π hπ h20 (by norm_num) T hT0
  rw [localDensityOf_binary_K0 hπ h2 ha T] at hK
  induction e with
  | zero => simp
  | succ e ih =>
    rw [localDensity_pow_sq_step (QuadForm.diag a) hQ π hπ h20 (by norm_num) T hT0 hstab e, ih]
    simp only [Nat.sub_self, pow_zero, inv_one, one_mul] at hK ⊢
    rw [← hK]
    push_cast
    ring

theorem sum_range_pow_of_sq_eq_one {χ : ℝ} (hχ : χ ^ 2 = 1) (e : ℕ) :
    ∑ j ∈ Finset.range (2 * e + 1), χ ^ j = 1 + e * (1 + χ) ∧
      ∑ j ∈ Finset.range (2 * e + 2), χ ^ j = (e + 1) * (1 + χ) := by
  induction e with
  | zero => simp; ring
  | succ e ih =>
    have h1 : χ ^ (2 * e + 1) = χ := by rw [pow_succ, pow_mul, hχ, one_pow, one_mul]
    have h2 : χ ^ (2 * e + 2) = 1 := by rw [pow_add, pow_mul, hχ, one_pow, one_mul]
    have h3 : χ ^ (2 * e + 3) = χ := by rw [pow_succ, h2, one_mul]
    constructor
    · rw [show 2 * (e + 1) + 1 = (2 * e + 2) + 1 by ring, Finset.sum_range_succ, ih.2, h2]
      push_cast; ring
    · rw [show 2 * (e + 1) + 2 = (2 * e + 2) + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
        ih.2, h2, h3]
      push_cast; ring

/-- **Binary densities at a non-dyadic unimodular prime:** for $\langle a_0, a_1\rangle$ with unit $a_i$, $\pi \nmid 2$, and
$m = \pi^v u$ ($u$ a unit), $\beta_\pi(m) = (1 - \chi/q)\sum_{j=0}^{v}\chi^j$, $\chi = \left(\frac{-a_0a_1}{\pi}\right)$ (`binChi`). The DVR form of the
`localDensity_good_binary`. -/
@[kb "hanke2004" "Table 1, p. 363; (5.7), p. 369 (n = 2)"]
theorem localDensity_binary_diag {a : Fin 2 → R} {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2) (ha : ∀ i, ¬ π ∣ a i)
    (hQ : (QuadForm.diag a).Nondegenerate) (u : R) (hu : IsUnit u) (v : ℕ) :
    localDensity (QuadForm.diag a) π (π ^ v * u) =
      (1 - (binChi a : ℝ) / (q R : ℝ)) * ∑ j ∈ Finset.range (v + 1), ((binChi a : ℝ)) ^ j := by
  have hu' : ¬ π ∣ u := fun h => hπ.not_isUnit (isUnit_of_dvd_unit h hu)
  have hχ : ((binChi a : ℝ)) ^ 2 = 1 := by exact_mod_cast binChi_sq hπ ha
  have hq : (0 : ℝ) < q R := by exact_mod_cast q_pos (R := R)
  have hK : (1 + (binChi a : ℝ)) * (1 - 1 / (q R : ℝ)) = (1 - (binChi a : ℝ) / q R) * (1 + binChi a) := by
    field_simp; linear_combination hχ
  obtain ⟨e, rfl | rfl⟩ := Nat.even_or_odd' v
  · rw [localDensity_binary_pow_sq hπ h2 ha hQ u hu.ne_zero e, localDensity_binary_unit hπ h2 ha u hu',
      (sum_range_pow_of_sq_eq_one hχ e).1, hK]
    ring
  · have hπu : π * u ≠ 0 := mul_ne_zero hπ.ne_zero hu.ne_zero
    rw [show π ^ (2 * e + 1) * u = π ^ (2 * e) * (π * u) by ring,
      localDensity_binary_pow_sq hπ h2 ha hQ _ hπu e,
      localDensity_diag_ord_one a π hπ h2 ha (π * u) (dvd_mul_right _ _) (by
        rintro ⟨c, hc⟩
        rw [pow_two, mul_assoc] at hc
        exact hu' ⟨c, mul_left_cancel₀ hπ.ne_zero hc⟩),
      show 2 * e + 1 + 1 = 2 * e + 2 by ring, (sum_range_pow_of_sq_eq_one hχ e).2]
    have h0 := (repCount_one_binary hπ h2 ha).1
    have h0' : (repCount (QuadForm.diag a) π 1 0 : ℝ) = q R + binChi a * (q R - 1) := by exact_mod_cast h0
    rw [h0', show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    field_simp
    first
      | linear_combination ((e : ℝ) + 1) * hχ
      | linear_combination (-((e : ℝ) + 1)) * hχ
      | linear_combination ((e : ℝ) + 1) * (q R : ℝ) * hχ
      | linear_combination (-((e : ℝ) + 1)) * (q R : ℝ) * hχ

end QuadFormsKB.LocalDensity.DVR

/-! ### The norm form $Q_b$ at the good primes of $F$ -/

namespace QuadFormsKB.Binary.Rel

open LocalDensity

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

/-- $\theta_b = b_0\sigma(b_1) - \sigma(b_0)b_1 \in \mathcal O_E$, with $\sigma\theta_b = -\theta_b$ and $\theta_b^2 = -\det H(Q_b)$. -/
def thetaB (b : Basis (Fin 2) (𝓞 F) (𝓞 E)) : 𝓞 E := b 0 * conjO F E (b 1) - conjO F E (b 0) * b 1

theorem conjO_conjO (x : 𝓞 E) : conjO F E (conjO F E x) = x := by
  apply FaithfulSMul.algebraMap_injective (𝓞 E) E
  rw [algebraMap_conjO, algebraMap_conjO, conj_conj]

theorem conjO_thetaB (b : Basis (Fin 2) (𝓞 F) (𝓞 E)) : conjO F E (thetaB b) = -thetaB b := by
  rw [thetaB, map_sub, map_mul, map_mul, conjO_conjO, conjO_conjO]; ring

theorem algebraMap_neg_hessian_det (b : Basis (Fin 2) (𝓞 F) (𝓞 E)) :
    algebraMap (𝓞 F) (𝓞 E) (-(normFormBasis b).hessian.det) = thetaB b ^ 2 := by
  apply FaithfulSMul.algebraMap_injective (𝓞 E) E
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E, map_neg, map_neg,
    hessian_det_normFormBasis_eq_norm, algebraMap_norm]
  simp only [thetaB, map_pow, map_sub, map_mul, algebraMap_conjO, conj_conj]
  ring

theorem nondegenerate_diag_units {R : Type*} [CommRing R] [IsDomain R] {a : Fin 2 → R} (ha : ∀ i, a i ≠ 0)
    (h2 : (2 : R) ≠ 0) : (QuadForm.diag a).Nondegenerate := by
  rw [QuadForm.Nondegenerate, QuadForm.hessian, QuadForm.diag, Matrix.diagonal_transpose,
    Matrix.diagonal_add, Matrix.det_diagonal, Fin.prod_univ_two]
  exact mul_ne_zero (by rw [← two_mul]; exact mul_ne_zero h2 (ha 0))
    (by rw [← two_mul]; exact mul_ne_zero h2 (ha 1))

/-- **Local densities of the norm form at the good primes of $F$** (the analogue over $F$ of `localDensity_good_binary`): for an
$\mathcal O_F$-basis $b$ of $\mathcal O_E$, $\mathfrak p \nmid 2\Delta_{E/F}(b)$ (`IsGoodPrimeNF`; such $\mathfrak p$ are unramified in $E$), and $\nu \ne 0$,
$$\beta_\mathfrak p(Q_b, \nu) = \Big(1 - \frac{\chi_{E/F}(\mathfrak p)}{N\mathfrak p}\Big)\sum_{j=0}^{v_\mathfrak p(\nu)}\chi_{E/F}(\mathfrak p)^j .$$ -/
@[kb "hanke2004" "Table 1, p. 363; (5.7), p. 369 (n = 2, over F); cf. localDensity_good_binary"]
theorem localDensity_normFormBasis_good (b : Basis (Fin 2) (𝓞 F) (𝓞 E)) (v : HeightOneSpectrum (𝓞 F))
    (hG : Siegel.IsGoodPrimeNF (normFormBasis b) v) {ν : 𝓞 F} (hν : ν ≠ 0) :
    NF.localDensity v (normFormBasis b) ν =
      (1 - (relChar E v : ℝ) / (Ideal.absNorm v.asIdeal : ℝ)) *
        ∑ j ∈ Finset.range (Siegel.ordNF v ν + 1), (relChar E v : ℝ) ^ j := by
  classical
  obtain ⟨a, ha, hc, u, hu, hprod⟩ := Siegel.goodPrimeShape_of_isGoodPrimeNF hG
  have h2 := Siegel.not_π_dvd_two hG.1
  have hπ := NF.irreducible_π v
  have ha0 : ∀ i, a i ≠ 0 := fun i h => ha i (h ▸ dvd_zero _)
  have hQ := nondegenerate_diag_units ha0 (NF.two_ne_zero' v)
  obtain ⟨w, hw, hιν⟩ := Siegel.ι_eq_pow_mul_unit v hν
  rw [Siegel.localDensityNF_eq_diag v hc, hιν, DVR.localDensity_binary_diag hπ h2 ha hQ w hw, NF.q_completion]
  -- the character
  have hχ : (DVR.binChi a : ℤ) = relChar E v := by
    have hs := Siegel.charNF_shape_even v (Q := normFormBasis b) even_two hG.1 hu hprod 1
    simp only [Fin.prod_univ_two, pow_one, neg_one_mul] at hs
    have hb : DVR.binChi a = Siegel.charNF v (-(normFormBasis b).hessian.det) := by
      unfold DVR.binChi; convert hs
    rw [hb, relChar_eq_charNF (conjO_thetaB b) (algebraMap_neg_hessian_det b) hG.1
      (fun h => hG.2 (neg_mem_iff.mp h))]
  rw [hχ]

theorem count_normalizedFactors_span_eq_ordNF (𝔭 : HeightOneSpectrum (𝓞 F)) {ν : 𝓞 F} (hν : ν ≠ 0) :
    Multiset.count 𝔭.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {ν})) =
      Siegel.ordNF 𝔭 ν := by
  obtain ⟨h1, h2⟩ := Siegel.mem_pow_ordNF 𝔭 hν
  exact Ideal.count_normalizedFactors_eq ((Ideal.span_singleton_le_iff_mem _).mpr h1)
    (fun h => h2 ((Ideal.span_singleton_le_iff_mem _).mp h))

open Classical in
/-- **The class sum by local densities, for $\nu$ prime to the bad primes** (Siegel's formula summed over all classes; the
analogue over $F$ of `binaryEulerCorr_coprime` with the ramified factors summed out). For an $\mathcal O_F$-basis
$b$ of $\mathcal O_E$ and $\nu \ne 0$ divisible only by good primes of $Q_b$ ($\mathfrak p \nmid 2\Delta_{E/F}(b)$):
$$\sum_{C}\sum_{\eta \in U_{E/F}} r_{(\mathfrak A_C,\ c_{C,\eta}N)}(\nu) = w_1\prod_{\mathfrak p \mid \nu}\frac{\beta_\mathfrak p(Q_b, \nu)}{1 - \chi_{E/F}(\mathfrak p)N\mathfrak p^{-1}},$$
$w_1 = \#\{u \in \mathcal O_E^\times : N(u) = 1\}$ ($= w_E$ in the CM case); the right side is the regularized-product convention
(the finite product of $\beta_\mathfrak p/(1 - \chi(\mathfrak p)N\mathfrak p^{-1})$; the remaining factors are absorbed in $L(1,\chi_{E/F})^{-1}$). -/
@[kb "siegel1935" "Hauptsatz (n = 2) [unverified]; hanke2004 (5.3); cf. binaryEulerCorr_coprime"]
theorem sum_repNumLat_eq_prod_localDensity [Finite (NormOneUnits F E)] (b : Basis (Fin 2) (𝓞 F) (𝓞 E))
    {ν : 𝓞 F} (hν : ν ≠ 0)
    (hgood : ∀ 𝔭 : HeightOneSpectrum (𝓞 F), ν ∈ 𝔭.asIdeal → Siegel.IsGoodPrimeNF (normFormBasis b) 𝔭) :
    ((∑ C : PNClass F E, ∑ η : unitQuot F E,
      repNumLat (scaleOf C η • normForm F E) (idealLat F (classRep E C.1 : Ideal (𝓞 E)))
        (algebraMap (𝓞 F) F ν) : ℕ) : ℝ) =
    Nat.card (NormOneUnits F E) * ∏ᶠ 𝔭 : HeightOneSpectrum (𝓞 F),
      (if ν ∈ 𝔭.asIdeal then
        NF.localDensity 𝔭 (normFormBasis b) ν / (1 - (relChar E 𝔭 : ℝ) / (Ideal.absNorm 𝔭.asIdeal : ℝ))
      else 1) := by
  classical
  have h := sum_repNumLat_eq_finprod (F := F) (E := E) hν
  have hspan : Ideal.span {ν} ≠ 0 := by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hν
  have hfin : (Function.mulSupport fun 𝔭 : HeightOneSpectrum (𝓞 F) => geomSum (relChar E 𝔭)
      (Multiset.count 𝔭.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {ν})))).Finite := by
    refine (Ideal.finite_factors hspan).subset fun 𝔭 h𝔭 => ?_
    by_contra hd
    apply h𝔭
    have : Multiset.count 𝔭.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {ν})) = 0 := by
      rw [Multiset.count_eq_zero]
      exact fun hm => hd (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hm)
    simp only [this, geomSum_zero]
  have h' := congrArg (Int.castRingHom ℝ) h
  have hmf := (Int.castRingHom ℝ).toMonoidHom.map_finprod hfin
  simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at hmf
  rw [map_mul, hmf] at h'
  simp only [eq_intCast, Int.cast_natCast] at h'
  rw [h']
  congr 1
  refine finprod_congr fun 𝔭 => ?_
  rw [count_normalizedFactors_span_eq_ordNF 𝔭 hν]
  split_ifs with h𝔭
  · rw [localDensity_normFormBasis_good b 𝔭 (hgood 𝔭 h𝔭) hν]
    have hN : (2 : ℝ) ≤ Ideal.absNorm 𝔭.asIdeal := by exact_mod_cast Siegel.two_le_normP_real 𝔭
    have hχ : (relChar E 𝔭 : ℝ) ≤ 1 := by
      rcases relChar_trichotomy (E := E) 𝔭 with h | h | h <;> rw [h] <;> norm_num
    have hden : (1 - (relChar E 𝔭 : ℝ) / (Ideal.absNorm 𝔭.asIdeal : ℝ)) ≠ 0 := by
      have : (relChar E 𝔭 : ℝ) / (Ideal.absNorm 𝔭.asIdeal : ℝ) < 1 := by
        rw [div_lt_one (by linarith)]; linarith
      linarith
    rw [mul_div_cancel_left₀ _ hden, geomSum]
    push_cast
    rfl
  · have : Siegel.ordNF 𝔭 ν = 0 := Siegel.ordNF_eq_zero 𝔭 h𝔭
    rw [this, geomSum_zero]
    simp

end QuadFormsKB.Binary.Rel
