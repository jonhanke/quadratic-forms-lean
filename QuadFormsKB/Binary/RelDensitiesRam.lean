import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Binary.RelDensitiesDyadic
import QuadFormsKB.LocalDensity.DyadicClosed
import QuadFormsKB.LocalDensity.DyadicBad

/-!
# Local densities of the norm form at the non-dyadic ramified primes

* **`DVR.localDensity_unit_of_rank_one`** (DVR, $\pi \nmid 2$): a binary form $Q$ with $\pi \mid \det H$ and a $\pi$-unit value
  has $\beta_\pi(m) = 1 + \chi(um)$ at every unit $m$, for a unit $u$ (the unit Jordan coefficient): its Jordan form is
  $\langle u, \pi^k w\rangle$ with $k \ge 1$, $Q \equiv ux^2 \pmod \pi$, and a unit is represented at level $1$ by $q(1 + \chi(um))$ vectors
  (`DVR.localDensity_unit_eq_level` at $e = 0$, all solutions being of Good type).
* **`localDensity_normFormBasis_ram`**: for $\mathfrak p \nmid 2$ ramified in $E$ and $\nu$ a $\mathfrak p$-unit,
  $$\beta_\mathfrak p(Q_b, \nu) = 1 + \left(\frac{\nu}{\mathfrak p}\right) \in \{0, 2\}$$
  (`Siegel.charNF`, the quadratic residue symbol). The unit $u$ is a square mod $\mathfrak p$ because $Q_b$ represents $1 = N(1)$.
  At $F = \mathbb Q$ this is `localDensity_ram` for the principal form ($\chi_p(f) = 1$) at $p \nmid m$.

Sources: Hanke (2004), Def. 3.1 and Lemma 3.2; Siegel (1935) §§1–2 [unverified]; cf. `BinaryDensitiesRam.lean`.
-/

open NumberField Module IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.LocalDensity.DVR

section FiniteField

variable {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]

theorem card_mul_sq_eq (hF : ringChar 𝔽 ≠ 2) {a : 𝔽} (ha : a ≠ 0) (c : 𝔽) :
    ((Finset.univ.filter fun y : 𝔽 => a * y ^ 2 = c).card : ℤ) = quadraticChar 𝔽 (a * c) + 1 := by
  have e : (Finset.univ.filter fun y : 𝔽 => a * y ^ 2 = c) = {y : 𝔽 | y ^ 2 = c / a}.toFinset := by
    ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset, Set.mem_setOf_eq]
    constructor
    · intro h; rw [← h]; field_simp
    · intro h; rw [h]; field_simp
  rw [e, quadraticChar_card_sqrts hF]
  congr 1
  have : c / a = a * c * (a⁻¹) ^ 2 := by field_simp
  rw [this, map_mul, quadraticChar_sq_one' (inv_ne_zero ha), mul_one]

theorem diagCountF_one (a c : 𝔽) :
    diagCountF ![a] c = ((Finset.univ.filter fun y : 𝔽 => a * y ^ 2 = c).card : ℤ) := by
  unfold diagCountF
  rw [← (Equiv.funUnique (Fin 1) 𝔽).symm.sum_comp, Finset.sum_boole]
  simp [Fin.sum_univ_one]

theorem diagCountF_zero_one (r : 𝔽) :
    diagCountF ![(0 : 𝔽)] r = if r = 0 then (Fintype.card 𝔽 : ℤ) else 0 := by
  rw [diagCountF_one]
  split_ifs with h
  · subst h; simp
  · rw [Finset.filter_false_of_mem (fun y _ => by rw [zero_mul]; exact Ne.symm h)]; simp

/-- A binary diagonal count with one zero coefficient: $\#\{x \in \mathbb F^2 : ax_0^2 = c\} = q(1 + \chi(ac))$. -/
theorem diagCountF_unit_zero (hF : ringChar 𝔽 ≠ 2) {a : 𝔽} (ha : a ≠ 0) (c : 𝔽) :
    diagCountF ![a, 0] c = (Fintype.card 𝔽 : ℤ) * (1 + quadraticChar 𝔽 (a * c)) := by
  have h := diagCountF_cons a ![(0 : 𝔽)] c
  rw [show (Fin.cons a ![(0 : 𝔽)] : Fin 2 → 𝔽) = ![a, 0] from rfl] at h
  rw [h]
  simp_rw [diagCountF_zero_one, sub_eq_zero]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  rw [add_comm, ← card_mul_sq_eq hF ha c]
  congr 2
  ext y; simp [eq_comm]

theorem diagCountF_zero_unit (hF : ringChar 𝔽 ≠ 2) {a : 𝔽} (ha : a ≠ 0) (c : 𝔽) :
    diagCountF ![0, a] c = (Fintype.card 𝔽 : ℤ) * (1 + quadraticChar 𝔽 (a * c)) := by
  have h := diagCountF_cons (0 : 𝔽) ![a] c
  rw [show (Fin.cons 0 ![a] : Fin 2 → 𝔽) = ![0, a] from rfl] at h
  rw [h]
  simp_rw [zero_mul, sub_zero, diagCountF_one]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_mul_sq_eq hF ha c, add_comm (1 : ℤ)]

end FiniteField

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Fintype (IsLocalRing.ResidueField R)] [DecidableEq (IsLocalRing.ResidueField R)]

open QuadForm Matrix

/-- **A binary form of residue rank one at a non-dyadic prime:** if $\pi \nmid 2$, $\pi \mid \det H(Q)$ and $Q$ takes a $\pi$-unit value,
there is a unit $u$ with $\beta_\pi(Q, m) = 1 + \chi(um)$ for every unit $m$ ($\chi$ the quadratic character of $R/\pi$). -/
@[kb "hanke2004" "Def. 3.1, Lemma 3.2; Table 1 (degenerate reduction)"]
theorem localDensity_unit_of_rank_one (Q : QuadForm R 2) (hQ : Q.Nondegenerate) {π : R} (hπ : Irreducible π)
    (h2 : ¬ π ∣ 2) (hdet : π ∣ Q.hessian.det) (hprim : ∃ x, ¬ π ∣ Q.eval x) :
    ∃ u : R, ¬ π ∣ u ∧ ∀ m : R, ¬ π ∣ m →
      localDensity Q π m = 1 + (quadraticChar (IsLocalRing.ResidueField R) (IsLocalRing.residue R (u * m)) : ℝ) := by
  classical
  have h20 : (2 : R) ≠ 0 := fun h => h2 (h ▸ dvd_zero _)
  obtain ⟨Q', P, w, hJ, hP, hE⟩ := exists_jordanFormW_isGLEquiv Q hQ π hπ h20
  have hP0 := hP h2
  subst hP0
  obtain ⟨-, -, -, hoff, -, hdiag⟩ := hJ
  have hnp : ∀ i : Fin 2, ¬ IsPaired (∅ : Finset (Fin 2 × Fin 2)) i := fun i ⟨e, he, _⟩ => by simp at he
  obtain ⟨u0, hu0, hu0u⟩ := hdiag 0 (hnp 0)
  obtain ⟨u1, hu1, hu1u⟩ := hdiag 1 (hnp 1)
  have hc01 : Q'.coeff 0 1 = 0 := hoff 0 1 (by decide) (by simp)
  have hc10 : Q'.coeff 1 0 = 0 := Q'.upper (by decide)
  -- values of Q'
  have heval : ∀ x : Fin 2 → R, Q'.eval x = Q'.coeff 0 0 * x 0 ^ 2 + Q'.coeff 1 1 * x 1 ^ 2 := by
    intro x
    simp [QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_two, hc01, hc10]
    ring
  -- det: w 0 + w 1 ≥ 1
  have hdet' : π ∣ Q'.hessian.det := by
    obtain ⟨v, -, hv⟩ := hE.det_hessian
    rw [hv]; exact dvd_mul_of_dvd_right hdet _
  have hdetQ' : Q'.hessian.det = 4 * π ^ (w 0 + w 1) * u0 * u1 := by
    rw [Matrix.det_fin_two]
    simp only [QuadForm.hessian, Matrix.add_apply, Matrix.transpose_apply, hc01, hc10, hu0, hu1]
    ring
  have hπu0 : ¬ π ∣ u0 := dvr_not_dvd_of_isUnit hπ hu0u
  have hπu1 : ¬ π ∣ u1 := dvr_not_dvd_of_isUnit hπ hu1u
  have h4 : ¬ π ∣ 4 := by
    intro h; rw [show (4 : R) = 2 * 2 by norm_num] at h
    rcases hπ.prime.dvd_or_dvd h with h | h <;> exact h2 h
  have hw : w 0 + w 1 ≠ 0 := by
    intro h0
    rw [hdetQ', h0, pow_zero, mul_one] at hdet'
    rcases hπ.prime.dvd_or_dvd hdet' with h | h
    · rcases hπ.prime.dvd_or_dvd h with h | h
      · exact h4 h
      · exact hπu0 h
    · exact hπu1 h
  -- a unit value: not both w ≥ 1
  have hprim' : ∃ x, ¬ π ∣ Q'.eval x := by
    obtain ⟨U, hU, hUQ⟩ := hE
    obtain ⟨x, hx⟩ := hprim
    refine ⟨U⁻¹ *ᵥ x, ?_⟩
    rw [hUQ, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU, Matrix.one_mulVec]
    exact hx
  have hone : w 0 = 0 ∨ w 1 = 0 := by
    by_contra hc
    push Not at hc
    obtain ⟨x, hx⟩ := hprim'
    apply hx
    rw [heval, hu0, hu1]
    exact dvd_add (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_pow_self π hc.1) _) _)
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_pow_self π hc.2) _) _)
  have hF : ringChar (IsLocalRing.ResidueField R) ≠ 2 := ringChar_residueField_ne_two hπ h2
  have hq : (0 : ℝ) < q R := by exact_mod_cast q_pos (R := R)
  have he : π ^ 0 ∣ 2 ∧ ¬ π ^ (0 + 1) ∣ 2 := ⟨by simp, by simpa using h2⟩
  -- the level-one count through a diagonal form with one zero coefficient
  have key : ∀ (a : Fin 2 → R), (∀ i j, π ^ 1 ∣ Q'.coeff i j - (QuadForm.diag a).coeff i j) →
      ∀ m, ¬ π ∣ m → localDensity Q π m = (repCount (QuadForm.diag a) π 1 m : ℝ) / q R := by
    intro a ha m hm
    rw [localDensity_unit_eq_level Q hQ π hπ h20 0 he hm 1 (by norm_num), ← hE.repCount_eq,
      repCount_congr_coeff Q' (QuadForm.diag a) π 1 ha (m' := m) (by simp)]
    norm_num
  rcases hone with h0 | h0
  · refine ⟨u0, hπu0, fun m hm => ?_⟩
    have hc : ∀ i j, π ^ 1 ∣ Q'.coeff i j - (QuadForm.diag ![u0, 0]).coeff i j := by
      have hw1 : 1 ≤ w 1 := by omega
      intro i j
      fin_cases i <;> fin_cases j <;> simp [QuadForm.diag, hc01, hc10, hu0, hu1, h0]
      exact dvd_mul_of_dvd_left (dvd_pow_self π (by omega)) _
    rw [key _ hc m hm]
    have hcnt := repCount_diag_one_eq ![u0, 0] hπ m
    have hres : (fun i => IsLocalRing.residue R ((![u0, 0] : Fin 2 → R) i)) = ![IsLocalRing.residue R u0, 0] := by
      funext i; fin_cases i <;> simp
    rw [hres, diagCountF_unit_zero hF ((residue_eq_zero_iff_dvd hπ u0).not.mpr hπu0)] at hcnt
    have hcnt' : (repCount (QuadForm.diag ![u0, 0]) π 1 m : ℝ) =
        (q R : ℝ) * (1 + quadraticChar (IsLocalRing.ResidueField R) (IsLocalRing.residue R u0 * IsLocalRing.residue R m)) := by
      have : (q R : ℤ) = Fintype.card (IsLocalRing.ResidueField R) := by
        rw [q, Nat.card_eq_fintype_card]
      exact_mod_cast hcnt.trans (by rw [this])
    rw [hcnt', map_mul (IsLocalRing.residue R)]
    field_simp
  · refine ⟨u1, hπu1, fun m hm => ?_⟩
    have hc : ∀ i j, π ^ 1 ∣ Q'.coeff i j - (QuadForm.diag ![0, u1]).coeff i j := by
      have hw0 : 1 ≤ w 0 := by omega
      intro i j
      fin_cases i <;> fin_cases j <;> simp [QuadForm.diag, hc01, hc10, hu0, hu1, h0]
      exact dvd_mul_of_dvd_left (dvd_pow_self π (by omega)) _
    rw [key _ hc m hm]
    have hcnt := repCount_diag_one_eq ![0, u1] hπ m
    have hres : (fun i => IsLocalRing.residue R ((![0, u1] : Fin 2 → R) i)) = ![0, IsLocalRing.residue R u1] := by
      funext i; fin_cases i <;> simp
    rw [hres, diagCountF_zero_unit hF ((residue_eq_zero_iff_dvd hπ u1).not.mpr hπu1)] at hcnt
    have hcnt' : (repCount (QuadForm.diag ![0, u1]) π 1 m : ℝ) =
        (q R : ℝ) * (1 + quadraticChar (IsLocalRing.ResidueField R) (IsLocalRing.residue R u1 * IsLocalRing.residue R m)) := by
      have : (q R : ℤ) = Fintype.card (IsLocalRing.ResidueField R) := by
        rw [q, Nat.card_eq_fintype_card]
      exact_mod_cast hcnt.trans (by rw [this])
    rw [hcnt', map_mul (IsLocalRing.residue R)]
    field_simp

end QuadFormsKB.LocalDensity.DVR

namespace QuadFormsKB.Binary.Rel

open LocalDensity

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

/-- The norm form $Q_b$ is nondegenerate (its discriminant is $-\det H = \Delta_{E/F}(b) \ne 0$, from the discriminant tower). -/
theorem hessian_det_normFormBasis_ne_zero (b : Basis (Fin 2) (𝓞 F) (𝓞 E)) : (normFormBasis b).hessian.det ≠ 0 := by
  intro h0
  have hΔ : Algebra.discr F (fun j => ((b j : 𝓞 E) : E)) = 0 := by
    rw [← neg_eq_zero, ← hessian_det_normFormBasis b, h0, map_zero]
  have := discr_tower b
  rw [hΔ, Algebra.norm_zero, mul_zero] at this
  exact discr_ne_zero E (by exact_mod_cast this)

/-- $Q_b$ represents $1 = N(1)$. -/
theorem exists_normFormBasis_eval_one (b : Basis (Fin 2) (𝓞 F) (𝓞 E)) :
    ∃ c : Fin 2 → 𝓞 F, (normFormBasis b).eval c = 1 := by
  refine ⟨b.repr 1, ?_⟩
  rw [normFormBasis_eval]
  have h := b.sum_repr 1
  rw [Fin.sum_univ_two] at h
  rw [h]
  exact map_one _

/-- **Local densities of the norm form at the non-dyadic ramified primes, $\nu$ a unit:** for $\mathfrak p \nmid 2$ ramified in $E$ and
$\nu \notin \mathfrak p$, $\beta_\mathfrak p(Q_b, \nu) = 1 + \left(\frac{\nu}{\mathfrak p}\right) \in \{0, 2\}$. -/
@[kb "hanke2004" "Def. 3.1, Lemma 3.2; cf. localDensity_ram"]
theorem localDensity_normFormBasis_ram (b : Basis (Fin 2) (𝓞 F) (𝓞 E)) {𝔭 : HeightOneSpectrum (𝓞 F)}
    (h2 : (2 : 𝓞 F) ∉ 𝔭.asIdeal) (hram : relChar E 𝔭 = 0) {ν : 𝓞 F} (hν : ν ∉ 𝔭.asIdeal) :
    NF.localDensity 𝔭 (normFormBasis b) ν = 1 + (Siegel.charNF 𝔭 ν : ℝ) := by
  classical
  set Q := NF.Qp 𝔭 (normFormBasis b)
  have hπ := NF.irreducible_π 𝔭
  have hπ2 : ¬ NF.π 𝔭 ∣ 2 := by
    intro h; apply h2; rw [show (2 : 𝓞 F) = 2 from rfl, ← NF.π_dvd_ι_iff, map_ofNat]; exact h
  have hQ : Q.Nondegenerate := NF.nondegenerate_Qp 𝔭 (hessian_det_normFormBasis_ne_zero b)
  have hdet : NF.π 𝔭 ∣ Q.hessian.det := by
    rw [NF.det_hessian_Qp, NF.π_dvd_ι_iff]; exact hessian_det_mem_of_ramified b hram
  obtain ⟨c, hc⟩ := exists_normFormBasis_eval_one b
  have hQc : Q.eval (fun i => NF.ι 𝔭 (c i)) = 1 := by
    rw [DVR.eval_map_apply, hc, map_one]
  obtain ⟨u, hu, hβ⟩ := DVR.localDensity_unit_of_rank_one Q hQ hπ hπ2 hdet
    ⟨_, by rw [hQc]; exact hπ.not_isUnit ∘ isUnit_of_dvd_one⟩
  have hu' : IsLocalRing.residue _ u ≠ 0 := (DVR.residue_eq_zero_iff_dvd hπ u).not.mpr hu
  -- χ(u) = 1, since Q represents 1
  have hχu : quadraticChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers F)) (IsLocalRing.residue _ u) = 1 := by
    rcases quadraticChar_dichotomy hu' with h | h
    · exact h
    · exfalso
      have h1 := hβ 1 (hπ.not_isUnit ∘ isUnit_of_dvd_one)
      rw [mul_one, h] at h1
      have h20 : (2 : 𝔭.adicCompletionIntegers F) ≠ 0 := NF.two_ne_zero' 𝔭
      rw [DVR.localDensity_unit_eq_level Q hQ (NF.π 𝔭) hπ h20 0 ⟨by simp, by simpa using hπ2⟩
        (hπ.not_isUnit ∘ isUnit_of_dvd_one) 1 (by norm_num)] at h1
      norm_num at h1
      have hfin := DVR.finite_quot_pow (NF.π 𝔭) hπ 1
      have : DVR.repCount Q (NF.π 𝔭) 1 1 ≠ 0 := by
        unfold DVR.repCount
        have : Finite (Fin 2 → 𝔭.adicCompletionIntegers F ⧸ Ideal.span {NF.π 𝔭 ^ 1}) := Pi.finite
        refine Nat.card_ne_zero.mpr ⟨⟨⟨fun j => Ideal.Quotient.mk _ (NF.ι 𝔭 (c j)), ?_⟩⟩, inferInstance⟩
        rw [DVR.evalIn_mk]; congr 1
      rcases h1 with h1 | h1
      · exact this (by exact_mod_cast h1)
      · exact absurd h1 (by exact_mod_cast (DVR.q_pos (R := 𝔭.adicCompletionIntegers F)).ne')
  rw [NF.localDensity_eq_completion, hβ _ (fun h => hν ((NF.π_dvd_ι_iff 𝔭 _).mp h)), map_mul, map_mul, hχu, one_mul]
  rfl

end QuadFormsKB.Binary.Rel
