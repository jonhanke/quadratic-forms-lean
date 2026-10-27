/-
# Weil's local identity at the good primes

**Layer:** a DVR $R$ with uniformizer $\pi$ and finite residue field (`LocalDensity/DVR*`), then the completions of
$\mathcal O_F$ (`LocalDensity/NF*`).

For $Q = \langle m\rangle \perp Q'$ (`splitForm`) Weil's fibration $O(V) \to \{v : Q(v) = m\}$, $g \mapsto g e_0$, with fibre
$O(e_0^\perp)$ gives, at a prime where $L = \mathfrak o e_0 \perp L'$ is unimodular and $m$ is a unit (one local type, of
weight $1$, and $|2m|_\pi = 1$),
$$\beta_\pi(L', L')\cdot\beta_\pi(L, m) = \beta_\pi(L, L)\qquad(\text{equivalently } \alpha_\pi(L')\,\beta_\pi(L, m) = \alpha_\pi(L)).$$
This file **proves** it from the closed forms (`localIdentity_good_odd`, `localIdentity_good_even`; over $F$:
`localIdentity_good`). It is the good-prime case of `LocalOrbitalIdentity` and confirms its normalization there
(the fibration constant $|2m|_\pi^{-n}$ is $1$). *Proof:* for $n + 1 = 2k + 1$ odd,
$2(1 - \chi q^{-k})\prod_{i<k-1}(1 - q^{-2(i+1)})\cdot(1 + \chi q^{-k}) = 2\prod_{i<k}(1 - q^{-2(i+1)})$ since the character of
$m$ by $L$ is that of $L'$: $(-1)^k\det(L)\,m = (-1)^k m^2\det(L')$ (`chiDiscT_splitForm`); for $n + 1 = 2k$ even, the
character of $L$ appears in both $\beta_\pi(L, L)$ and $\beta_\pi(L, m)$.
-/
import QuadFormsKB.Tamagawa.MassInduction

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.LocalDensity.DVR

open QuadForm Tamagawa

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}

local notation "𝔽" => IsLocalRing.ResidueField R
local notation "res" => IsLocalRing.residue R

theorem not_dvd_det_splitForm {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2) {m : R} (hm : ¬ π ∣ m)
    {Q' : QuadForm R n} (hdet : ¬ π ∣ Q'.hessian.det) : ¬ π ∣ (splitForm m Q').hessian.det := by
  rw [det_hessian_splitForm]
  intro h
  rcases hπ.prime.dvd_or_dvd h with h | h
  · rcases hπ.prime.dvd_or_dvd h with h | h
    · exact h2 h
    · exact hm h
  · exact hdet h

theorem res_ne_zero_of_not_dvd {π : R} (hπ : Irreducible π) {a : R} (ha : ¬ π ∣ a) : res a ≠ 0 := by
  intro h
  apply ha
  rw [IsLocalRing.residue_eq_zero_iff] at h
  exact (hπ.maximalIdeal_eq ▸ h : a ∈ Ideal.span {π}) |> Ideal.mem_span_singleton.mp

/-- **The character of $m$ by $\langle m\rangle\perp Q'$ is the discriminant character of $Q'$** ($Q'$ in $2k$ variables):
$\chi((-1)^k\,D_{Q}\,m) = \chi((-1)^k\,m^2 D_{Q'}) = \chi((-1)^k D_{Q'})$. -/
theorem chiDiscT_splitForm [Fintype 𝔽] [DecidableEq 𝔽] {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
    (k : ℕ) {m : R} (hm : ¬ π ∣ m) (Q' : QuadForm R (2 * k)) :
    chiDiscT (splitForm m Q') m = chiDisc Q' := by
  have h2F : (2 : 𝔽) ≠ 0 := by
    have := res_ne_zero_of_not_dvd hπ h2; rwa [map_ofNat] at this
  have hmF : res m ≠ 0 := res_ne_zero_of_not_dvd hπ hm
  unfold chiDiscT chiDisc resGramDet
  rw [det_hessian_splitForm, show (2 * k + 1 - 1) / 2 = k by omega, show 2 * k / 2 = k by omega]
  rw [show (-1 : 𝔽) ^ k * (res (2 * m * Q'.hessian.det) / 2 ^ (2 * k + 1)) * res m =
    (-1) ^ k * (res Q'.hessian.det / 2 ^ (2 * k)) * res m ^ 2 by
      simp only [map_mul, map_ofNat]
      field_simp
      ring, map_mul, quadraticChar_sq_one' hmF, mul_one]

theorem chiDisc_sq [Fintype 𝔽] [DecidableEq 𝔽] {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
    {Q : QuadForm R n} (hdet : ¬ π ∣ Q.hessian.det) : (chiDisc Q : ℝ) ^ 2 = 1 := by
  have h2F : (2 : 𝔽) ≠ 0 := by
    have := res_ne_zero_of_not_dvd hπ h2; rwa [map_ofNat] at this
  have hne : (-1 : 𝔽) ^ (n / 2) * resGramDet Q ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) ?_
    unfold resGramDet
    exact div_ne_zero (res_ne_zero_of_not_dvd hπ hdet) (pow_ne_zero _ h2F)
  have := quadraticChar_sq_one hne
  unfold chiDisc
  exact_mod_cast this

/-- **Weil's local identity at a good prime, odd rank** ($Q = \langle m\rangle \perp Q'$ in $2k+1$ variables, $k \ge 1$,
$\pi \nmid 2m\det H_{Q'}$): $\beta_\pi(Q', Q')\,\beta_\pi(Q, m) = \beta_\pi(Q, Q)$. -/
@[kb "weil1982" "§3.4 (local fibration, good primes) [unverified]"]
theorem localIdentity_good_odd [Fintype 𝔽] [DecidableEq 𝔽] {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
    (k : ℕ) (hk : 1 ≤ k) {m : R} (hm : ¬ π ∣ m) (Q' : QuadForm R (2 * k)) (hdet : ¬ π ∣ Q'.hessian.det) :
    localDensityForm Q' Q' π * localDensity (splitForm m Q') π m =
      localDensityForm (splitForm m Q') (splitForm m Q') π := by
  have hdet' := not_dvd_det_splitForm hπ h2 hm hdet
  rw [localDensityForm_self_even π k hk Q' hπ h2 hdet,
    localDensity_odd_unit_of_unimodular (splitForm m Q') π hπ h2 hdet' (odd_two_mul_add_one k) m hm,
    localDensityForm_self_odd π k (splitForm m Q') hπ h2 hdet', chiDiscT_splitForm hπ h2 k hm Q',
    show (2 * k + 1 - 1) / 2 = k by omega]
  have hχ := chiDisc_sq hπ h2 hdet
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [show j + 1 - 1 = j by omega, Finset.prod_range_succ]
  have hq : (0 : ℝ) < q R := by exact_mod_cast q_pos
  have hq' : (q R : ℝ) ^ (j + 1) ≠ 0 := pow_ne_zero _ hq.ne'
  rw [show ((q R : ℝ)) ^ (2 * (j + 1)) = ((q R : ℝ) ^ (j + 1)) ^ 2 by ring]
  set x := (q R : ℝ) ^ (j + 1)
  set c := (chiDisc Q' : ℝ)
  set P := ∏ i ∈ Finset.range j, (1 - ((q R : ℝ) ^ (2 * (i + 1)))⁻¹)
  have key : (1 - c * x⁻¹) * (1 + c / x) = 1 - (x ^ 2)⁻¹ := by
    field_simp
    linear_combination (-1 : ℝ) * hχ
  rw [show 2 * (1 - c * x⁻¹) * P * (1 + c / x) = 2 * P * ((1 - c * x⁻¹) * (1 + c / x)) by ring, key]
  ring

/-- **Weil's local identity at a good prime, even rank** ($Q = \langle m\rangle \perp Q'$ in $2k$ variables, $k \ge 1$,
$\pi \nmid 2m\det H_{Q'}$): $\beta_\pi(Q', Q')\,\beta_\pi(Q, m) = \beta_\pi(Q, Q)$. -/
@[kb "weil1982" "§3.4 (local fibration, good primes) [unverified]"]
theorem localIdentity_good_even [Fintype 𝔽] [DecidableEq 𝔽] {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
    (j : ℕ) {m : R} (hm : ¬ π ∣ m) (Q' : QuadForm R (2 * j + 1)) (hdet : ¬ π ∣ Q'.hessian.det) :
    localDensityForm Q' Q' π * localDensity (splitForm m Q') π m =
      localDensityForm (splitForm m Q') (splitForm m Q') π := by
  have hdet' := not_dvd_det_splitForm hπ h2 hm hdet
  have h1 := localDensityForm_self_even π (j + 1) (by omega) (splitForm m Q') hπ h2 hdet'
  have h3 := localDensity_even_unit_of_unimodular (splitForm m Q') π hπ h2 hdet' (by omega)
    ⟨j + 1, by omega⟩ m hm
  rw [localDensityForm_self_odd π j Q' hπ h2 hdet, h3, h1, show (2 * j + 1 + 1) / 2 = j + 1 by omega,
    show j + 1 - 1 = j by omega]
  ring

end QuadFormsKB.LocalDensity.DVR

namespace QuadFormsKB.Tamagawa

open LocalDensity

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))

/-- **Weil's local identity at the good primes of $F$:** for $Q_0 = \langle m\rangle\perp Q_0'$ over $\mathcal O_F$, $n \ge 2$, and
$\mathfrak p \nmid 2m\det H_{Q_0'}$,
$$\alpha_\mathfrak p(L', L')\cdot\beta_\mathfrak p(L, m) = \alpha_\mathfrak p(L, L),$$
($\alpha$ = `NF.siegelDensity`, $\beta$ = `NF.localDensity`): the local factor of `LocalOrbitalIdentity` is $1$ at these
primes, as it must be (one local type of weight $1$, $|2m|_\mathfrak p = 1$). -/
@[kb "weil1982" "§3.4 (local fibration, good primes) [unverified]"]
theorem localIdentity_good (hn : 2 ≤ n) (m : NumberField.RingOfIntegers F)
    (Q₀' : QuadForm (NumberField.RingOfIntegers F) n) (h2 : (2 : NumberField.RingOfIntegers F) ∉ v.asIdeal)
    (hm : m ∉ v.asIdeal) (hd : Q₀'.hessian.det ∉ v.asIdeal) :
    NF.siegelDensity v Q₀' Q₀' * NF.localDensity v (splitForm m Q₀') m =
      NF.siegelDensity v (splitForm m Q₀') (splitForm m Q₀') := by
  classical
  have hπ := NF.irreducible_π v
  have h2' := not_dvd_two_of_good v h2
  have hd' := not_dvd_det_of_good v Q₀' hd
  have hm' : ¬ NF.π v ∣ NF.ι v m := by rw [NF.π_dvd_ι_iff]; exact hm
  have hsplit : NF.Qp v (splitForm m Q₀') = splitForm (NF.ι v m) (NF.Qp v Q₀') := map_splitForm _ _ _
  unfold NF.siegelDensity
  simp only [↓reduceIte]
  rw [NF.localDensityForm_eq_completion, NF.localDensityForm_eq_completion, NF.localDensity_eq_completion,
    hsplit]
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · have := DVR.localIdentity_good_odd hπ h2' k (by omega) hm' (NF.Qp v Q₀') hd'
    rw [← this]; ring
  · have := DVR.localIdentity_good_even hπ h2' k hm' (NF.Qp v Q₀') hd'
    rw [← this]; ring

end QuadFormsKB.Tamagawa
