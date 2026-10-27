/-
# $\tau(SO_1) = 1$: the bad-prime local densities in rank one

**Layer:** DVR (a discrete valuation ring with finite residue field and $2 \ne 0$) and $\mathcal O_F$ at a finite prime
$\mathfrak p$, dyadic included. Closes the one *Gap* recorded in `RankOneNF.lean`.

**Proves**
* `DVR` level: for $Q = c\,x_0^2$ with $\pi^t \,\Vert\, 2$, $\pi^e \,\Vert\, c$,
  `repCount_rankOne`: $A_{\pi^k}(Q, \langle c\rangle) = 2q^{t+e}$ for $k \ge 2t + e + 1$ (the number of $x \bmod \pi^k$ with
  $cx^2 \equiv c$: $x \equiv \pm 1 \bmod \pi^{k-t-e}$, two disjoint cosets), and
  `localDensityForm_rankOne`: $\beta_\pi(\langle c\rangle, \langle c\rangle) = 2q^{t+e}$.
* `siegelDensity_rankOne`: for $Q_0 = \langle c\rangle$ over $\mathcal O_F$ and $\mathfrak p^d \,\Vert\, 2c$,
  $\alpha_\mathfrak p(Q_0, Q_0) = N\mathfrak p^{d}$ ($=N\mathfrak p^{v_\mathfrak p(2c)}$), at **every** finite prime.
-/
import QuadFormsKB.LocalDensity.NFFormDensity
import QuadFormsKB.Tamagawa.RankOneNF

open NumberField IsDedekindDomain Filter Matrix

set_option linter.unusedSectionVars false
set_option linter.deprecated false

noncomputable section

namespace QuadFormsKB.Tamagawa.TauSOOne

open QuadFormsKB QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR

section DVRPart

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem dvd_sq_sub_one_iff {π w : R} (hπ : Irreducible π) {t : ℕ} (h2 : (2 : R) = π ^ t * w)
    (hw : IsUnit w) {j m : ℕ} (hm : m = j + t) (htj : t < j) (x : R) :
    π ^ m ∣ x ^ 2 - 1 ↔ π ^ j ∣ x - 1 ∨ π ^ j ∣ x + 1 := by
  have hfac : x ^ 2 - 1 = (x - 1) * (x + 1) := by ring
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h1'⟩ := hcon
    have hy0 : x - 1 ≠ 0 := fun h0 => h1 (by rw [h0]; exact dvd_zero _)
    have hz0 : x + 1 ≠ 0 := fun h0 => h1' (by rw [h0]; exact dvd_zero _)
    obtain ⟨a, y', hy, hy'⟩ := dvr_eq_pow_mul_unit hπ hy0
    obtain ⟨b, z', hz, hz'⟩ := dvr_eq_pow_mul_unit hπ hz0
    have haj : a < j := by
      by_contra hh; push Not at hh
      exact h1 (by rw [hy]; exact Dvd.dvd.mul_right (pow_dvd_pow π hh) _)
    have hbj : b < j := by
      by_contra hh; push Not at hh
      exact h1' (by rw [hz]; exact Dvd.dvd.mul_right (pow_dvd_pow π hh) _)
    have hab : m ≤ a + b := by
      by_contra hh; push Not at hh
      apply dvr_not_pow_succ_dvd hπ (hy'.mul hz') (a + b)
      have h3 : π ^ (a + b + 1) ∣ π ^ m := pow_dvd_pow π hh
      refine h3.trans ?_
      rw [hfac, hy, hz] at h
      rw [show π ^ (a + b) * (y' * z') = π ^ a * y' * (π ^ b * z') by ring]
      exact h
    have hta : t < a := by omega
    have htb : t < b := by omega
    have d1 : π ^ (t + 1) ∣ x - 1 := by
      rw [hy]; exact Dvd.dvd.mul_right (pow_dvd_pow π hta) _
    have d2 : π ^ (t + 1) ∣ x + 1 := by
      rw [hz]; exact Dvd.dvd.mul_right (pow_dvd_pow π htb) _
    have d3 : π ^ (t + 1) ∣ π ^ t * w := by
      rw [← h2, show (2 : R) = (x + 1) - (x - 1) by ring]
      exact dvd_sub d2 d1
    exact dvr_not_pow_succ_dvd hπ hw t d3
  · obtain ⟨s, hs⟩ : ∃ s, j = t + s := ⟨j - t, by omega⟩
    subst hm
    subst hs
    rintro (⟨a, ha⟩ | ⟨a, ha⟩)
    · have e2 : x + 1 = π ^ t * (π ^ s * a + w) := by
        have : x + 1 = (x - 1) + 2 := by ring
        rw [this, ha, h2]; ring
      exact ⟨a * (π ^ s * a + w), by rw [hfac, ha, e2]; ring⟩
    · have e2 : x - 1 = π ^ t * (π ^ s * a - w) := by
        have : x - 1 = (x + 1) - 2 := by ring
        rw [this, ha, h2]; ring
      exact ⟨a * (π ^ s * a - w), by rw [hfac, ha, e2]; ring⟩

end DVRPart


section CountPart

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- Number of residue classes mod `π^k` that are `≡ a` mod `π^j`: `q^(k-j)`. -/
theorem card_coset {π : R} (hπ : Irreducible π) {j k : ℕ} (hjk : j ≤ k) (a : R) :
    Nat.card {x : R ⧸ Ideal.span {π ^ k} // ∃ y : R, x = Ideal.Quotient.mk _ (a + π ^ j * y)} =
      q R ^ (k - j) := by
  classical
  rw [← natCard_quot_pow π hπ (k - j)]
  let lift : R ⧸ Ideal.span {π ^ (k - j)} → R := fun z => (Ideal.Quotient.mk_surjective z).choose
  have hlift : ∀ z, Ideal.Quotient.mk _ (lift z) = z := fun z => (Ideal.Quotient.mk_surjective z).choose_spec
  let g : R ⧸ Ideal.span {π ^ (k - j)} → {x : R ⧸ Ideal.span {π ^ k} //
      ∃ y : R, x = Ideal.Quotient.mk _ (a + π ^ j * y)} :=
    fun z => ⟨Ideal.Quotient.mk _ (a + π ^ j * lift z), _, rfl⟩
  have hkey : ∀ y y' : R, Ideal.Quotient.mk (Ideal.span {π ^ k}) (a + π ^ j * y) =
      Ideal.Quotient.mk (Ideal.span {π ^ k}) (a + π ^ j * y') ↔
      Ideal.Quotient.mk (Ideal.span {π ^ (k - j)}) y = Ideal.Quotient.mk (Ideal.span {π ^ (k - j)}) y' := by
    intro y y'
    rw [Ideal.Quotient.eq, Ideal.Quotient.eq, Ideal.mem_span_singleton, Ideal.mem_span_singleton,
      show a + π ^ j * y - (a + π ^ j * y') = π ^ j * (y - y') by ring,
      show π ^ k = π ^ j * π ^ (k - j) by rw [← pow_add]; congr 1; omega]
    exact mul_dvd_mul_iff_left (pow_ne_zero _ hπ.ne_zero)
  symm
  refine Nat.card_congr (Equiv.ofBijective g ⟨?_, ?_⟩)
  · intro z z' h
    have h' := congrArg Subtype.val h
    have := (hkey _ _).mp h'
    rwa [hlift, hlift] at this
  · rintro ⟨x, y, rfl⟩
    refine ⟨Ideal.Quotient.mk _ y, Subtype.ext ?_⟩
    show Ideal.Quotient.mk _ (a + π ^ j * lift (Ideal.Quotient.mk _ y)) = _
    rw [hkey, hlift]

end CountPart

section MainPart

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem mem_coset_iff {π : R} {j k : ℕ} (hjk : j ≤ k) (a r : R) :
    (∃ y : R, Ideal.Quotient.mk (Ideal.span {π ^ k}) r = Ideal.Quotient.mk _ (a + π ^ j * y)) ↔
      π ^ j ∣ r - a := by
  constructor
  · rintro ⟨y, hy⟩
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at hy
    have h1 : π ^ j ∣ r - (a + π ^ j * y) := (pow_dvd_pow π hjk).trans hy
    have : r - a = (r - (a + π ^ j * y)) + π ^ j * y := by ring
    rw [this]; exact dvd_add h1 (dvd_mul_right _ _)
  · rintro ⟨y, hy⟩
    exact ⟨y, by rw [show r = a + π ^ j * y by linear_combination hy]⟩

/-- **The count of square roots of `c` mod `π^k`**: `A_k = 2 q^(t+e)` for `k = j + t + e`, `t < j`. -/
theorem repCount_rankOne {π w u : R} (hπ : Irreducible π) [Finite (IsLocalRing.ResidueField R)]
    {t e j k : ℕ} (h2 : (2 : R) = π ^ t * w) (hw : IsUnit w) {c : R} (hc : c = π ^ e * u) (hu : IsUnit u)
    (Q : QuadForm R 1) (hQ : Q.coeff 0 0 = c) (hk : k = j + t + e) (htj : t < j) :
    DVR.repCount Q π k c = 2 * q R ^ (t + e) := by
  classical
  have : Finite (R ⧸ Ideal.span {π ^ k}) := finite_quot_pow π hπ k
  set K := R ⧸ Ideal.span {π ^ k} with hK
  let S1 : Set K := {z | ∃ y : R, z = Ideal.Quotient.mk _ (1 + π ^ j * y)}
  let S2 : Set K := {z | ∃ y : R, z = Ideal.Quotient.mk _ (-1 + π ^ j * y)}
  have hjk : j ≤ k := by omega
  have hcond : ∀ r : R, Q.evalIn K (fun _ => Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ c ↔
      Ideal.Quotient.mk _ r ∈ S1 ∪ S2 := by
    intro r
    have hev : Q.evalIn K (fun _ => Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (c * r * r) := by
      simp [QuadForm.evalIn, hQ]
      rfl
    rw [hev, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    show _ ↔ (∃ y, _ = _) ∨ (∃ y, _ = _)
    rw [mem_coset_iff hjk, mem_coset_iff hjk, sub_neg_eq_add]
    have h3 : c * r * r - c = π ^ e * (u * (r ^ 2 - 1)) := by rw [hc]; ring
    rw [h3, show π ^ k = π ^ e * π ^ (j + t) by rw [← pow_add]; congr 1; omega,
      mul_dvd_mul_iff_left (pow_ne_zero _ hπ.ne_zero), hu.dvd_mul_left]
    exact dvd_sq_sub_one_iff hπ h2 hw rfl htj r
  have hdisj : Disjoint S1 S2 := by
    rw [Set.disjoint_left]
    intro z h1 h2'
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    have a1 : π ^ j ∣ r - 1 := (mem_coset_iff hjk 1 r).mp h1
    have a2 : π ^ j ∣ r + 1 := by
      have := (mem_coset_iff hjk (-1) r).mp h2'
      rwa [sub_neg_eq_add] at this
    have a3 : π ^ (t + 1) ∣ π ^ t * w := by
      rw [← h2, show (2 : R) = (r + 1) - (r - 1) by ring]
      exact dvd_sub ((pow_dvd_pow π htj).trans a2) ((pow_dvd_pow π htj).trans a1)
    exact dvr_not_pow_succ_dvd hπ hw t a3
  have e1 : Nat.card {x : Fin 1 → K // Q.evalIn K x = Ideal.Quotient.mk _ c} =
      Nat.card ↥(S1 ∪ S2) := by
    refine Nat.card_congr ((Equiv.funUnique (Fin 1) K).subtypeEquiv ?_)
    intro x
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (x 0)
    have hx : x = fun _ => Ideal.Quotient.mk _ r := funext fun i => by
      fin_cases i; simpa using hr.symm
    rw [hx, hcond]
    simp
  have c1 : Nat.card ↥S1 = q R ^ (t + e) := by
    have := card_coset hπ hjk 1
    rw [show k - j = t + e by omega] at this
    exact this
  have c2 : Nat.card ↥S2 = q R ^ (t + e) := by
    have := card_coset hπ hjk (-1)
    rw [show k - j = t + e by omega] at this
    exact this
  unfold DVR.repCount
  rw [e1, Nat.card_coe_set_eq, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
    ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, c1, c2]
  ring

/-- **The self-density of a rank-one form**: `β_π(⟨c⟩, ⟨c⟩) = 2 q^(t+e)` where `π^t ∥ 2`, `π^e ∥ c`. -/
theorem localDensityForm_rankOne {π w u : R} (hπ : Irreducible π) [Finite (IsLocalRing.ResidueField R)]
    {t e : ℕ} (h2 : (2 : R) = π ^ t * w) (hw : IsUnit w) {c : R} (hc : c = π ^ e * u) (hu : IsUnit u)
    (Q : QuadForm R 1) (hQ : Q.coeff 0 0 = c) :
    localDensityForm Q Q π = 2 * (q R : ℝ) ^ (t + e) := by
  have hQu : Q = unary c := by
    refine QuadForm.ext_upper fun i j _ => ?_
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simpa [unary, QuadForm.diag] using hQ
  have hrep : ∀ k, repCountForm Q Q π k = DVR.repCount Q π k c := by
    intro k
    have := repCountForm_unary Q π k c
    rwa [← hQu] at this
  unfold localDensityForm
  refine Filter.Tendsto.limUnder_eq (Filter.Tendsto.congr' ?_ tendsto_const_nhds)
  filter_upwards [Filter.eventually_ge_atTop (2 * t + e + 1)] with k hk
  rw [hrep, repCount_rankOne hπ h2 hw hc hu Q hQ (j := k - t - e) (by omega) (by omega)]
  simp

end MainPart

section NFPart

open QuadFormsKB.LocalDensity.NF

variable {F : Type*} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

/-- **The local statement behind $\tau(SO_1) = 1$** (rank one, every finite prime, dyadic included):
$\alpha_\mathfrak p(\langle c\rangle, \langle c\rangle) = N\mathfrak p^{d}$ where $\mathfrak p^d \,\Vert\, 2c$. -/
@[kb "siegel1935" "α_p in rank one, ε = 1/2 [unverified]"]
theorem siegelDensity_rankOne (Q₀ : QuadForm (𝓞 F) 1) {d : ℕ}
    (hd : 2 * Q₀.coeff 0 0 ∈ v.asIdeal ^ d) (hd' : 2 * Q₀.coeff 0 0 ∉ v.asIdeal ^ (d + 1)) :
    LocalDensity.NF.siegelDensity v Q₀ Q₀ = (Ideal.absNorm v.asIdeal : ℝ) ^ d := by
  have hc0 : Q₀.coeff 0 0 ≠ 0 := fun h => hd' (by rw [h, mul_zero]; exact Submodule.zero_mem _)
  obtain ⟨t, w, h2, hw⟩ := dvr_eq_pow_mul_unit (irreducible_π v) (two_ne_zero' v)
  obtain ⟨e, u, hc, hu⟩ := dvr_eq_pow_mul_unit (irreducible_π v) (ι_ne_zero v hc0)
  have hexp : ι v (2 * Q₀.coeff 0 0) = π v ^ (t + e) * (w * u) := by
    rw [map_mul, map_ofNat, h2, hc]; ring
  have hdte : d = t + e := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · apply hd'
      rw [← π_pow_dvd_ι_iff, hexp]
      exact Dvd.dvd.mul_right (pow_dvd_pow _ h) _
    · have h1 := (π_pow_dvd_ι_iff v d _).mpr hd
      rw [hexp] at h1
      have h3 : π v ^ (t + e + 1) ∣ π v ^ (t + e) * (w * u) := (pow_dvd_pow _ h).trans h1
      exact dvr_not_pow_succ_dvd (irreducible_π v) (hw.mul hu) _ h3
  subst hdte
  unfold LocalDensity.NF.siegelDensity
  rw [if_pos rfl, NF.localDensityForm_eq_completion,
    localDensityForm_rankOne (irreducible_π v) h2 hw hc hu (Qp v Q₀) (by simp [Qp, QuadForm.map]),
    q_completion]
  ring

end NFPart

section Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Lattices

variable {F : Type} [Field F] [NumberField F]

theorem absNorm_span_eq_prod_embeddings (x : 𝓞 F) :
    (Ideal.absNorm (Ideal.span {x}) : ℝ) = ∏ σ : F →ₐ[ℚ] ℂ, ‖σ (x : F)‖ := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ (x : F)
  have h2 := congrArg (fun z : ℂ => ‖z‖) h
  simp only [norm_prod] at h2
  rw [← h2, Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs]
  have h3 : ((Algebra.norm ℤ x : ℤ) : ℝ) = (((Algebra.norm ℚ (x : F)) : ℚ) : ℝ) := by
    rw [← Algebra.coe_norm_int]; norm_cast
  rw [h3]
  simp

theorem prod_maxPow_eq {x : 𝓞 F} (hx : x ≠ 0) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 F), x ∈ v.asIdeal → v ∈ S) :
    ∏ v ∈ S, (Ideal.absNorm (v.maxPowDividing (Ideal.span {x})) : ℝ) =
      ∏ σ : F →ₐ[ℚ] ℂ, ‖σ (x : F)‖ := by
  have hI : Ideal.span {x} ≠ 0 := by simpa using hx
  rw [← absNorm_span_eq_prod_embeddings]
  conv_rhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI]
  have hp := ((Nat.castRingHom ℝ).toMonoidHom.comp
      (Ideal.absNorm : Ideal (𝓞 F) →*₀ ℕ).toMonoidHom).map_finprod_of_preimage_one
    (fun I hI => by simpa using hI) (fun v : HeightOneSpectrum (𝓞 F) => v.maxPowDividing (Ideal.span {x}))
  rw [show ((Ideal.absNorm (∏ᶠ v : HeightOneSpectrum (𝓞 F), v.maxPowDividing (Ideal.span {x})) : ℕ) : ℝ) =
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), (Ideal.absNorm (v.maxPowDividing (Ideal.span {x})) : ℝ) from hp]
  symm
  refine finprod_eq_prod_of_mulSupport_subset _ ?_
  intro v hv
  rw [Finset.mem_coe]
  apply hS
  rw [← Ideal.dvd_span_singleton]
  simp only [Function.mem_mulSupport, maxPowDividing, map_pow, Nat.cast_pow,
    ← pow_zero (Ideal.absNorm v.asIdeal : ℝ)] at hv
  refine (Associates.count_ne_zero_iff_dvd hI (irreducible v)).1 <| fun h => hv ?_
  rw [h]

/-- The local density in terms of the maximal power of `p` dividing `2c`. -/
theorem siegelDensity_rankOne_maxPow (Q₀ : QuadForm (𝓞 F) 1) (hc : Q₀.coeff 0 0 ≠ 0)
    (v : HeightOneSpectrum (𝓞 F)) :
    LocalDensity.NF.siegelDensity v Q₀ Q₀ =
      (Ideal.absNorm (v.maxPowDividing (Ideal.span {2 * Q₀.coeff 0 0})) : ℝ) := by
  have hx : (2 * Q₀.coeff 0 0 : 𝓞 F) ≠ 0 := mul_ne_zero two_ne_zero hc
  have hI : Ideal.span {2 * Q₀.coeff 0 0} ≠ ⊥ := by simpa using hx
  have hfin := Ideal.finiteMultiplicity v.isPrime.ne_top hI
  rw [maxPowDividing_eq_pow_multiplicity hI, map_pow, Nat.cast_pow]
  refine siegelDensity_rankOne v Q₀ (d := multiplicity v.asIdeal (Ideal.span {2 * Q₀.coeff 0 0})) ?_ ?_
  · have := pow_multiplicity_dvd v.asIdeal (Ideal.span {2 * Q₀.coeff 0 0})
    rw [Ideal.dvd_iff_le] at this
    exact this (Ideal.mem_span_singleton_self _)
  · intro hmem
    refine hfin.not_pow_dvd_of_multiplicity_lt (m := multiplicity v.asIdeal
      (Ideal.span {2 * Q₀.coeff 0 0}) + 1) (Nat.lt_succ_self _) ?_
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hmem

theorem hessian_det_rankOne (Q₀ : QuadForm (𝓞 F) 1) : Q₀.hessian.det = 2 * Q₀.coeff 0 0 := by
  rw [Matrix.det_unique]; simp [QuadForm.hessian]; ring

theorem detGram_rankOne (Q₀ : QuadForm (𝓞 F) 1) (σ : F →ₐ[ℚ] ℂ) :
    detGram Q₀ σ = ‖σ ((Q₀.coeff 0 0 : 𝓞 F) : F)‖ := by
  have h2 : (algebraMap (𝓞 F) F) 2 = 2 := map_ofNat _ 2
  rw [detGram, hessian_det_rankOne]
  congr 1
  simp [h2]

/-- **$\tau(SO_1) = 1$: the Tamagawa measure of $K_{SO_1}$ is $1$** (rank one, every number field, dyadic
primes included): $\prod_\sigma\frac1{2|\sigma(c)|}\cdot\prod_{\mathfrak p\mid 2c}N\mathfrak p^{v_\mathfrak p(2c)} = 1$,
the product formula for $2c$. -/
@[kb "weil1982" "§3.7, τ(SO_1) = 1 [unverified]"]
theorem tamagawaK_rankOne_eq_one (Q₀ : QuadForm (𝓞 F) 1) (hQ : Q₀.Nondegenerate) :
    tamagawaK Q₀ = 1 := by
  have hdet := hessian_det_rankOne Q₀
  have hc : Q₀.coeff 0 0 ≠ 0 := by
    intro h0; apply hQ; rw [hdet, h0, mul_zero]
  have hx : (2 * Q₀.coeff 0 0 : 𝓞 F) ≠ 0 := mul_ne_zero two_ne_zero hc
  rw [RankOne.tamagawaK_rankOne Q₀ hQ,
    Finset.prod_congr rfl fun v _ => siegelDensity_rankOne_maxPow Q₀ hc v,
    prod_maxPow_eq hx _ (fun v hv => by
      rw [Set.Finite.mem_toFinset]
      show 2 * Q₀.hessian.det ∈ v.asIdeal
      rw [hdet]; exact Ideal.mul_mem_left _ _ hv),
    ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun σ _ => ?_
  have hσ : ‖σ ((Q₀.coeff 0 0 : 𝓞 F) : F)‖ ≠ 0 := by
    rw [norm_ne_zero_iff, map_ne_zero]
    exact_mod_cast hc
  rw [detGram_rankOne]
  have : ‖σ (((2 * Q₀.coeff 0 0 : 𝓞 F)) : F)‖ = 2 * ‖σ ((Q₀.coeff 0 0 : 𝓞 F) : F)‖ := by
    have h2 : (algebraMap (𝓞 F) F) 2 = 2 := map_ofNat _ 2
    simp [h2, map_ofNat]
  rw [this]
  field_simp

/-- **$\tau(SO_1) = 1$** (`tauSO`, $Q_0 = \langle c\rangle$ over $\mathcal O_F$ totally positive, $L = \mathcal O_F$
integral). Closes the rank-one gap. -/
@[kb "weil1982" "§3.7, τ(SO_1) = 1 [unverified]"]
theorem tauSO_rankOne_eq_one (Q₀ : QuadForm (𝓞 F) 1) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (hLi : IsIntegral (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F 1).1) : tauSO Q₀ = 1 := by
  rw [RankOne.tauSO_rankOne Q₀ hQ hpd hLi, tamagawaK_rankOne_eq_one Q₀ hQ]

end Global

end QuadFormsKB.Tamagawa.TauSOOne
