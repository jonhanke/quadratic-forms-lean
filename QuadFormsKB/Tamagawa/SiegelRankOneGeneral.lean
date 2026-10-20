import QuadFormsKB.Tamagawa.SiegelRankOne

/-!
# Siegel's formula in rank one, general represented number $m = c\,s^2$

`SiegelRankOne.lean` proves the corrected rank-one Siegel formula only at $m = c$.  Here it is extended to
every represented $m = c s^2$ over $\mathcal O_F$ (and the value $0$ when $m$ is not $c$ times a square).

* **DVR count** (`repCount_rankOne_sq`, `localDensity_rankOne_sq`): for $2s = \pi^{t}w$, $c = \pi^e u$ (units $w,u$),
  $\#\{x \bmod \pi^k : c x^2 \equiv c s^2\} = 2 q^{t+e}$ for $k \ge 2t + e + 1$; the congruence $x^2 \equiv s^2 \pmod{\pi^{j+t}}$
  is $x \equiv \pm s \pmod{\pi^j}$ (`dvd_sq_sub_sq_iff`).  Hence $\beta_\mathfrak p(\langle c\rangle, cs^2) = 2N\mathfrak p^{v_\mathfrak p(2cs)}$
  at **every** finite prime (`localDensity_rankOne_sq_maxPow`).
* **Product formula** (`siegelProductOne_sq`): $\beta_\sigma(cs^2)/2 = 1/(2|\sigma(cs)|)$, so
  $\mathcal S_1(cs^2) = \prod_\sigma\frac{1}{2|\sigma(cs)|}\prod_\mathfrak p N\mathfrak p^{v_\mathfrak p(2cs)} = 1$, the product formula for $2cs$.
* **Result** (`siegelFormulaOne_sq`): $\mathrm{repMass}(\mathcal O_F, cs^2) = \mathrm{Mass}(\mathcal O_F)\cdot 2\,\mathcal S_1(cs^2)$ for every $s \ne 0$, and
  `repMass_rankOne_eq_zero` ($=0$) when $m \notin c\,\mathcal O_F^2$.
* **Over $\mathbb Z$** (`siegelFormulaOne_int`): for every $m \ge 1$, $r_{\mathrm{gen}}(\langle a\rangle, m) = 2\,\mathcal S_1(m)$, with
  $\mathcal S_1 = 1$ if $m = ak^2$ and $\mathcal S_1 = 0$ otherwise (a vanishing Euler factor, `exists_eulerFactor_eq_zero`); this
  is the corrected form of `Siegel.RankOne.siegel_rank_one_dichotomy`, whose literal product diverges exactly when $m$ is represented.
-/

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false
set_option linter.deprecated false

noncomputable section

namespace QuadFormsKB.Tamagawa.SiegelRankOne

open Lattices QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR QuadFormsKB.Tamagawa.TauSOOne

section DVRPart

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- **Square roots of $s^2$ modulo $\pi^{j+t}$** ($\pi^t \,\Vert\, 2s$, $t < j$):
$\pi^{j+t} \mid x^2 - s^2 \iff \pi^j \mid x - s \lor \pi^j \mid x + s$.  (`TauSOOne.dvd_sq_sub_one_iff` is the case $s = 1$.) -/
theorem dvd_sq_sub_sq_iff {π w : R} (hπ : Irreducible π) {t : ℕ} {s : R} (h2 : 2 * s = π ^ t * w)
    (hw : IsUnit w) {j m : ℕ} (hm : m = j + t) (htj : t < j) (x : R) :
    π ^ m ∣ x ^ 2 - s ^ 2 ↔ π ^ j ∣ x - s ∨ π ^ j ∣ x + s := by
  have hfac : x ^ 2 - s ^ 2 = (x - s) * (x + s) := by ring
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h1'⟩ := hcon
    have hy0 : x - s ≠ 0 := fun h0 => h1 (by rw [h0]; exact dvd_zero _)
    have hz0 : x + s ≠ 0 := fun h0 => h1' (by rw [h0]; exact dvd_zero _)
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
    have d1 : π ^ (t + 1) ∣ x - s := by
      rw [hy]; exact Dvd.dvd.mul_right (pow_dvd_pow π hta) _
    have d2 : π ^ (t + 1) ∣ x + s := by
      rw [hz]; exact Dvd.dvd.mul_right (pow_dvd_pow π htb) _
    have d3 : π ^ (t + 1) ∣ π ^ t * w := by
      rw [← h2, show 2 * s = (x + s) - (x - s) by ring]
      exact dvd_sub d2 d1
    exact dvr_not_pow_succ_dvd hπ hw t d3
  · obtain ⟨s', hs⟩ : ∃ s', j = t + s' := ⟨j - t, by omega⟩
    subst hm
    subst hs
    rintro (⟨a, ha⟩ | ⟨a, ha⟩)
    · have e2 : x + s = π ^ t * (π ^ s' * a + w) := by
        have : x + s = (x - s) + 2 * s := by ring
        rw [this, ha, h2]; ring
      exact ⟨a * (π ^ s' * a + w), by rw [hfac, ha, e2]; ring⟩
    · have e2 : x - s = π ^ t * (π ^ s' * a - w) := by
        have : x - s = (x + s) - 2 * s := by ring
        rw [this, ha, h2]; ring
      exact ⟨a * (π ^ s' * a - w), by rw [hfac, ha, e2]; ring⟩

/-- **The count of solutions of $c x^2 \equiv c s^2 \pmod{\pi^k}$**: $A_k = 2q^{t+e}$ for $k = j + t + e$, $t < j$,
where $\pi^t \,\Vert\, 2s$ and $\pi^e \,\Vert\, c$ (generalizes `TauSOOne.repCount_rankOne`, the case $s = 1$). -/
theorem repCount_rankOne_sq {π w u : R} (hπ : Irreducible π) [Finite (IsLocalRing.ResidueField R)]
    {t e j k : ℕ} {s : R} (h2 : 2 * s = π ^ t * w) (hw : IsUnit w) {c : R} (hc : c = π ^ e * u) (hu : IsUnit u)
    (Q : QuadForm R 1) (hQ : Q.coeff 0 0 = c) (hk : k = j + t + e) (htj : t < j) :
    DVR.repCount Q π k (c * s ^ 2) = 2 * q R ^ (t + e) := by
  classical
  have : Finite (R ⧸ Ideal.span {π ^ k}) := finite_quot_pow π hπ k
  set K := R ⧸ Ideal.span {π ^ k} with hK
  let S1 : Set K := {z | ∃ y : R, z = Ideal.Quotient.mk _ (s + π ^ j * y)}
  let S2 : Set K := {z | ∃ y : R, z = Ideal.Quotient.mk _ (-s + π ^ j * y)}
  have hjk : j ≤ k := by omega
  have hcond : ∀ r : R, Q.evalIn K (fun _ => Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (c * s ^ 2) ↔
      Ideal.Quotient.mk _ r ∈ S1 ∪ S2 := by
    intro r
    have hev : Q.evalIn K (fun _ => Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (c * r * r) := by
      simp [QuadForm.evalIn, hQ]
      rfl
    rw [hev, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    show _ ↔ (∃ y, _ = _) ∨ (∃ y, _ = _)
    rw [mem_coset_iff hjk, mem_coset_iff hjk, sub_neg_eq_add]
    have h3 : c * r * r - c * s ^ 2 = π ^ e * (u * (r ^ 2 - s ^ 2)) := by rw [hc]; ring
    rw [h3, show π ^ k = π ^ e * π ^ (j + t) by rw [← pow_add]; congr 1; omega,
      mul_dvd_mul_iff_left (pow_ne_zero _ hπ.ne_zero), hu.dvd_mul_left]
    exact dvd_sq_sub_sq_iff hπ h2 hw rfl htj r
  have hdisj : Disjoint S1 S2 := by
    rw [Set.disjoint_left]
    intro z h1 h2'
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    have a1 : π ^ j ∣ r - s := (mem_coset_iff hjk s r).mp h1
    have a2 : π ^ j ∣ r + s := by
      have := (mem_coset_iff hjk (-s) r).mp h2'
      rwa [sub_neg_eq_add] at this
    have a3 : π ^ (t + 1) ∣ π ^ t * w := by
      rw [← h2, show 2 * s = (r + s) - (r - s) by ring]
      exact dvd_sub ((pow_dvd_pow π htj).trans a2) ((pow_dvd_pow π htj).trans a1)
    exact dvr_not_pow_succ_dvd hπ hw t a3
  have e1 : Nat.card {x : Fin 1 → K // Q.evalIn K x = Ideal.Quotient.mk _ (c * s ^ 2)} =
      Nat.card ↥(S1 ∪ S2) := by
    refine Nat.card_congr ((Equiv.funUnique (Fin 1) K).subtypeEquiv ?_)
    intro x
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (x 0)
    have hx : x = fun _ => Ideal.Quotient.mk _ r := funext fun i => by
      fin_cases i; simpa using hr.symm
    rw [hx, hcond]
    simp
  have c1 : Nat.card ↥S1 = q R ^ (t + e) := by
    have := card_coset hπ hjk s
    rw [show k - j = t + e by omega] at this
    exact this
  have c2 : Nat.card ↥S2 = q R ^ (t + e) := by
    have := card_coset hπ hjk (-s)
    rw [show k - j = t + e by omega] at this
    exact this
  unfold DVR.repCount
  rw [e1, Nat.card_coe_set_eq, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
    ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, c1, c2]
  ring

/-- **The local density at $c s^2$ of a rank-one form**: $\beta_\pi(\langle c\rangle, cs^2) = 2q^{t+e}$ where
$\pi^t \,\Vert\, 2s$ and $\pi^e \,\Vert\, c$. -/
theorem localDensity_rankOne_sq {π w u : R} (hπ : Irreducible π) [Finite (IsLocalRing.ResidueField R)]
    {t e : ℕ} {s : R} (h2 : 2 * s = π ^ t * w) (hw : IsUnit w) {c : R} (hc : c = π ^ e * u) (hu : IsUnit u)
    (Q : QuadForm R 1) (hQ : Q.coeff 0 0 = c) :
    DVR.localDensity Q π (c * s ^ 2) = 2 * (q R : ℝ) ^ (t + e) := by
  unfold DVR.localDensity
  refine Filter.Tendsto.limUnder_eq (Filter.Tendsto.congr' ?_ tendsto_const_nhds)
  filter_upwards [Filter.eventually_ge_atTop (2 * t + e + 1)] with k hk
  rw [repCount_rankOne_sq hπ h2 hw hc hu Q hQ (j := k - t - e) (by omega) (by omega)]
  simp

end DVRPart

section NFPart

open QuadFormsKB.LocalDensity.NF IsDedekindDomain.HeightOneSpectrum

variable {F : Type} [Field F] [NumberField F]

local notation "QFof" Q₀ => QuadForm.map (algebraMap (𝓞 F) F) Q₀

/-- **The local density of $\langle c\rangle$ at $cs^2$ over $\mathcal O_F$**, in terms of $\mathfrak p^d \,\Vert\, 2cs$:
$\beta_\mathfrak p(\langle c\rangle, cs^2) = 2\,N\mathfrak p^{d}$, at **every** finite prime (dyadic included). -/
theorem localDensity_rankOne_sq_pow (Q₀ : QuadForm (𝓞 F) 1) (v : HeightOneSpectrum (𝓞 F)) {s : 𝓞 F} (hs : s ≠ 0)
    {d : ℕ} (hd : 2 * (Q₀.coeff 0 0 * s) ∈ v.asIdeal ^ d) (hd' : 2 * (Q₀.coeff 0 0 * s) ∉ v.asIdeal ^ (d + 1)) :
    NF.localDensity v Q₀ (Q₀.coeff 0 0 * s ^ 2) = 2 * (Ideal.absNorm v.asIdeal : ℝ) ^ d := by
  have hc0 : Q₀.coeff 0 0 ≠ 0 := fun h => hd' (by rw [h, zero_mul, mul_zero]; exact Submodule.zero_mem _)
  obtain ⟨t, w, h2, hw⟩ := dvr_eq_pow_mul_unit (irreducible_π v)
    (show ι v (2 * s) ≠ 0 from ι_ne_zero v (mul_ne_zero two_ne_zero hs))
  rw [map_mul, map_ofNat] at h2
  obtain ⟨e, u, hc, hu⟩ := dvr_eq_pow_mul_unit (irreducible_π v) (ι_ne_zero v hc0)
  have hexp : ι v (2 * (Q₀.coeff 0 0 * s)) = π v ^ (t + e) * (w * u) := by
    rw [show 2 * (Q₀.coeff 0 0 * s) = Q₀.coeff 0 0 * (2 * s) by ring, map_mul, map_mul, map_ofNat, h2, hc]; ring
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
  rw [NF.localDensity_eq_completion, map_mul, map_pow,
    localDensity_rankOne_sq (irreducible_π v) h2 hw hc hu (Qp v Q₀) (by simp [Qp, QuadForm.map]), q_completion]

/-- The factor of $\mathfrak p$ in terms of the maximal power of $\mathfrak p$ dividing $2cs$. -/
theorem localDensity_rankOne_sq_maxPow (Q₀ : QuadForm (𝓞 F) 1) (v : HeightOneSpectrum (𝓞 F)) {s : 𝓞 F}
    (hc : Q₀.coeff 0 0 ≠ 0) (hs : s ≠ 0) :
    NF.localDensity v Q₀ (Q₀.coeff 0 0 * s ^ 2) / 2 =
      (Ideal.absNorm (v.maxPowDividing (Ideal.span {2 * (Q₀.coeff 0 0 * s)})) : ℝ) := by
  have hx : (2 * (Q₀.coeff 0 0 * s) : 𝓞 F) ≠ 0 := mul_ne_zero two_ne_zero (mul_ne_zero hc hs)
  have hI : Ideal.span {2 * (Q₀.coeff 0 0 * s)} ≠ ⊥ := by simpa using hx
  have hfin := Ideal.finiteMultiplicity v.isPrime.ne_top hI
  rw [maxPowDividing_eq_pow_multiplicity hI, map_pow, Nat.cast_pow]
  rw [localDensity_rankOne_sq_pow Q₀ v hs
    (d := multiplicity v.asIdeal (Ideal.span {2 * (Q₀.coeff 0 0 * s)})) ?_ ?_]
  · ring
  · have := pow_multiplicity_dvd v.asIdeal (Ideal.span {2 * (Q₀.coeff 0 0 * s)})
    rw [Ideal.dvd_iff_le] at this
    exact this (Ideal.mem_span_singleton_self _)
  · intro hmem
    refine hfin.not_pow_dvd_of_multiplicity_lt (m := multiplicity v.asIdeal
      (Ideal.span {2 * (Q₀.coeff 0 0 * s)}) + 1) (Nat.lt_succ_self _) ?_
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hmem

/-- $\beta_\sigma(cs^2)/2 = 1/(2|\sigma(cs)|)$ in rank one. -/
theorem archRepDensity_rankOne_sq (Q₀ : QuadForm (𝓞 F) 1) (hc : Q₀.coeff 0 0 ≠ 0) {s : 𝓞 F} (hs : s ≠ 0)
    (σ : F →ₐ[ℚ] ℂ) :
    archRepDensity 1 ‖σ (algebraMap (𝓞 F) F (Q₀.coeff 0 0 * s ^ 2))‖ (detGram Q₀ σ) / 2 =
      1 / (2 * ‖σ (algebraMap (𝓞 F) F (Q₀.coeff 0 0 * s))‖) := by
  have hd := TauSOOne.detGram_rankOne Q₀ σ
  have ha : 0 < ‖σ ((Q₀.coeff 0 0 : 𝓞 F) : F)‖ := by
    rw [norm_pos_iff, map_ne_zero]; exact_mod_cast hc
  have hb : 0 < ‖σ ((s : 𝓞 F) : F)‖ := by
    rw [norm_pos_iff, map_ne_zero]; exact_mod_cast hs
  have e1 : ‖σ (algebraMap (𝓞 F) F (Q₀.coeff 0 0 * s ^ 2))‖ = ‖σ ((Q₀.coeff 0 0 : 𝓞 F) : F)‖ * ‖σ ((s : 𝓞 F) : F)‖ ^ 2 := by
    simp [map_mul, map_pow, norm_mul, norm_pow]
  have e2 : ‖σ (algebraMap (𝓞 F) F (Q₀.coeff 0 0 * s))‖ = ‖σ ((Q₀.coeff 0 0 : 𝓞 F) : F)‖ * ‖σ ((s : 𝓞 F) : F)‖ := by
    simp [map_mul, norm_mul]
  rw [e1, e2, hd, archRepDensity]
  have h1 : Real.pi ^ (((1 : ℕ) : ℝ) / 2) / Real.Gamma (((1 : ℕ) : ℝ) / 2) = 1 := by
    have : Real.pi ^ (((1 : ℕ) : ℝ) / 2) = Real.sqrt Real.pi := by
      rw [Real.sqrt_eq_rpow]; norm_num
    rw [this]; norm_num [Real.Gamma_one_half_eq]
    exact Real.sqrt_ne_zero'.mpr Real.pi_pos
  set a := ‖σ ((Q₀.coeff 0 0 : 𝓞 F) : F)‖
  set b := ‖σ ((s : 𝓞 F) : F)‖
  have h2 : (a * b ^ 2) ^ ((((1 : ℕ) : ℝ) - 2) / 2) * a ^ (-(1 / 2 : ℝ)) = (a * b)⁻¹ := by
    rw [show ((((1 : ℕ) : ℝ) - 2) / 2) = -(1 / 2 : ℝ) by norm_num, Real.mul_rpow ha.le (sq_nonneg b),
      Real.rpow_neg ha.le, Real.rpow_neg (sq_nonneg b), ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
      Real.sqrt_sq hb.le]
    have hsa : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
    have hsa2 : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha.le
    field_simp
    nlinarith [hsa2]
  rw [mul_assoc, h2, h1]
  field_simp

end NFPart

section Global

open QuadFormsKB.LocalDensity.NF IsDedekindDomain.HeightOneSpectrum

variable {F : Type} [Field F] [NumberField F]

local notation "QFof" Q₀ => QuadForm.map (algebraMap (𝓞 F) F) Q₀

theorem absNorm_maxPow_eq_one {x : 𝓞 F} (hx : x ≠ 0) (v : HeightOneSpectrum (𝓞 F)) (hv : x ∉ v.asIdeal) :
    (Ideal.absNorm (v.maxPowDividing (Ideal.span {x})) : ℝ) = 1 := by
  have hI : Ideal.span {x} ≠ 0 := by simpa using hx
  by_contra hne
  apply hv
  rw [← Ideal.dvd_span_singleton]
  simp only [maxPowDividing, map_pow, Nat.cast_pow, ← pow_zero (Ideal.absNorm v.asIdeal : ℝ)] at hne
  refine (Associates.count_ne_zero_iff_dvd hI (irreducible v)).1 <| fun h => hne ?_
  rw [h]

/-- **$\mathcal S_1(cs^2) = 1$: the product formula for $2cs$.** For $Q_0 = \langle c\rangle$ nondegenerate and $s \ne 0$,
$$\mathcal S_1(cs^2) = \prod_\sigma\frac{1}{2|\sigma(cs)|}\cdot\prod_{\mathfrak p}N\mathfrak p^{v_\mathfrak p(2cs)} = 1.$$ -/
@[kb "weil1982" "§3.7, τ(SO_1) = 1 (general represented m) [unverified]"]
theorem siegelProductOne_sq (Q₀ : QuadForm (𝓞 F) 1) (hQ : Q₀.Nondegenerate) {s : 𝓞 F} (hs : s ≠ 0) :
    siegelProductOne Q₀ (Q₀.coeff 0 0 * s ^ 2) = 1 := by
  have hc : Q₀.coeff 0 0 ≠ 0 := by
    intro h0; apply hQ; rw [TauSOOne.hessian_det_rankOne, h0, mul_zero]
  set x : 𝓞 F := 2 * (Q₀.coeff 0 0 * s) with hxdef
  have hx : x ≠ 0 := mul_ne_zero two_ne_zero (mul_ne_zero hc hs)
  have hfin : {v : HeightOneSpectrum (𝓞 F) | x ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {x})
      (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])).subset ?_
    intro v hv
    exact Ideal.dvd_span_singleton.mpr hv
  rw [siegelProductOne]
  rw [Finset.prod_congr rfl fun σ _ => archRepDensity_rankOne_sq Q₀ hc hs σ]
  have hfun : (fun v : HeightOneSpectrum (𝓞 F) => NF.localDensity v Q₀ (Q₀.coeff 0 0 * s ^ 2) / 2) =
      fun v => (Ideal.absNorm (v.maxPowDividing (Ideal.span {x})) : ℝ) :=
    funext fun v => localDensity_rankOne_sq_maxPow Q₀ v hc hs
  rw [hfun, tprod_eq_prod (s := hfin.toFinset) (fun v hv => absNorm_maxPow_eq_one hx v (by simpa using hv)),
    prod_maxPow_eq hx hfin.toFinset (fun v hv => by simpa using hv), ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun σ _ => ?_
  have hσ : ‖σ (algebraMap (𝓞 F) F (Q₀.coeff 0 0 * s))‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact (map_ne_zero σ).mpr ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr (mul_ne_zero hc hs))
  have : ‖σ ((x : 𝓞 F) : F)‖ = 2 * ‖σ (algebraMap (𝓞 F) F (Q₀.coeff 0 0 * s))‖ := by
    have h2 : (algebraMap (𝓞 F) F) 2 = 2 := map_ofNat _ 2
    simp [hxdef, h2, map_ofNat]
  rw [this]
  field_simp

/-- **$r_{\mathcal O_F}(cs^2) = 2$** for $Q_0 = \langle c\rangle$, $c, s \ne 0$: the solutions of $cx^2 = cs^2$ in $\mathcal O_F$ are $x = \pm s$. -/
theorem repCount_rankOne_sq_eq (Q₀ : QuadForm (𝓞 F) 1) (hc : Q₀.coeff 0 0 ≠ 0) {s : 𝓞 F} (hs : s ≠ 0) :
    Tamagawa.repCount (QFof Q₀) (stdLat F 1) (algebraMap (𝓞 F) F (Q₀.coeff 0 0 * s ^ 2)) = 2 := by
  have hcF : algebraMap (𝓞 F) F (Q₀.coeff 0 0) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hc
  have hsF : algebraMap (𝓞 F) F s ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hs
  have hset : {v : Fin 1 → F | v ∈ (stdLat F 1).1 ∧
      (QFof Q₀).eval v = algebraMap (𝓞 F) F (Q₀.coeff 0 0 * s ^ 2)} =
      {fun _ => algebraMap (𝓞 F) F s, fun _ => -algebraMap (𝓞 F) F s} := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨-, h⟩
      rw [eval_rankOne, map_mul, map_pow] at h
      have h1 : (v 0 - algebraMap (𝓞 F) F s) * (v 0 + algebraMap (𝓞 F) F s) = 0 := by
        have : algebraMap (𝓞 F) F (Q₀.coeff 0 0) * (v 0 ^ 2 - algebraMap (𝓞 F) F s ^ 2) = 0 := by
          linear_combination h
        rcases mul_eq_zero.mp this with h0 | h0
        · exact absurd h0 hcF
        · linear_combination h0
      rcases mul_eq_zero.mp h1 with h2 | h2
      · left; funext i; fin_cases i; simpa [sub_eq_zero] using h2
      · right; funext i; fin_cases i; simpa [add_eq_zero_iff_eq_neg] using h2
    · rintro (rfl | rfl)
      · exact ⟨fun i => ⟨s, rfl⟩, by rw [eval_rankOne]; simp [map_mul, map_pow]⟩
      · exact ⟨fun i => ⟨-s, by simp⟩, by rw [eval_rankOne]; simp [map_mul, map_pow]⟩
  unfold Tamagawa.repCount
  have : Nat.card {v : Fin 1 → F // v ∈ (stdLat F 1).1 ∧
      (QFof Q₀).eval v = algebraMap (𝓞 F) F (Q₀.coeff 0 0 * s ^ 2)} =
      Set.ncard {v : Fin 1 → F | v ∈ (stdLat F 1).1 ∧
        (QFof Q₀).eval v = algebraMap (𝓞 F) F (Q₀.coeff 0 0 * s ^ 2)} :=
    Nat.card_coe_set_eq _
  rw [this, hset, Set.ncard_pair]
  intro h
  have : algebraMap (𝓞 F) F s = -algebraMap (𝓞 F) F s := congrFun h 0
  exact hsF (self_eq_neg.mp this)

/-- **No representations when $m \notin c\,\mathcal O_F^2$.** -/
theorem repCount_rankOne_eq_zero (Q₀ : QuadForm (𝓞 F) 1) {m : 𝓞 F}
    (h : ∀ s : 𝓞 F, m ≠ Q₀.coeff 0 0 * s ^ 2) :
    Tamagawa.repCount (QFof Q₀) (stdLat F 1) (algebraMap (𝓞 F) F m) = 0 := by
  unfold Tamagawa.repCount
  rw [Nat.card_eq_zero]
  left
  constructor
  rintro ⟨v, hv, hev⟩
  obtain ⟨y, hy⟩ := hv 0
  rw [eval_rankOne, ← hy] at hev
  apply h y
  apply IsFractionRing.injective (𝓞 F) F
  rw [← hev]
  simp [map_mul, map_pow]

/-- **$\mathrm{repMass}(\mathcal O_F, cs^2) = 1$** for $s \ne 0$. -/
theorem repMass_rankOne_sq (Q₀ : QuadForm (𝓞 F) 1) (hc : Q₀.coeff 0 0 ≠ 0) {s : 𝓞 F} (hs : s ≠ 0) :
    repMass (QFof Q₀) (stdLat F 1) (algebraMap (𝓞 F) F (Q₀.coeff 0 0 * s ^ 2)) = 1 := by
  have hc' : (QFof Q₀).coeff 0 0 ≠ 0 := by simpa [QuadForm.map] using hc
  rw [repMass, RankOne.genusClasses_rankOne hc', finsum_mem_singleton]
  change ((Tamagawa.repCount (QFof Q₀) (stdLat F 1) _ : ℕ) : ℝ) / (Nat.card (autLat (QFof Q₀) (stdLat F 1).1) : ℝ) = 1
  rw [repCount_rankOne_sq_eq Q₀ hc hs, RankOne.card_autLat_rankOne hc']
  norm_num

/-- **$\mathrm{repMass}(\mathcal O_F, m) = 0$ when $m \notin c\,\mathcal O_F^2$.** -/
theorem repMass_rankOne_eq_zero (Q₀ : QuadForm (𝓞 F) 1) (hc : Q₀.coeff 0 0 ≠ 0) {m : 𝓞 F}
    (h : ∀ s : 𝓞 F, m ≠ Q₀.coeff 0 0 * s ^ 2) :
    repMass (QFof Q₀) (stdLat F 1) (algebraMap (𝓞 F) F m) = 0 := by
  have hc' : (QFof Q₀).coeff 0 0 ≠ 0 := by simpa [QuadForm.map] using hc
  rw [repMass, RankOne.genusClasses_rankOne hc', finsum_mem_singleton]
  change ((Tamagawa.repCount (QFof Q₀) (stdLat F 1) _ : ℕ) : ℝ) / (Nat.card (autLat (QFof Q₀) (stdLat F 1).1) : ℝ) = 0
  rw [repCount_rankOne_eq_zero Q₀ h]
  simp

/-- **Siegel's formula in rank one at every represented number $m = cs^2$** ($s \ne 0$; correct form, any number field):
$$\mathrm{repMass}(\mathcal O_F, cs^2) = \mathrm{Mass}(\mathcal O_F)\cdot\bigl(2\,\mathcal S_1(cs^2)\bigr),$$
the genus average being $2 = |O_1(F)|\,\mathcal S_1(cs^2)$ with $\mathcal S_1(cs^2) = 1$ (`siegelProductOne_sq`).  The case $s = 1$ is
`siegelFormulaOne_self`.  (The literal `SiegelFormulaAt` is false at $N = 1$.) -/
@[kb "siegel1935" "Hauptsatz, n = 1, general represented m (ε = 1/2, trivial SO_1) [unverified]"]
theorem siegelFormulaOne_sq (Q₀ : QuadForm (𝓞 F) 1) (hQ : Q₀.Nondegenerate) {s : 𝓞 F} (hs : s ≠ 0) :
    repMass (QFof Q₀) (stdLat F 1) (algebraMap (𝓞 F) F (Q₀.coeff 0 0 * s ^ 2)) =
      mass (QFof Q₀) (stdLat F 1) * (2 * siegelProductOne Q₀ (Q₀.coeff 0 0 * s ^ 2)) := by
  have hc : Q₀.coeff 0 0 ≠ 0 := by
    intro h0; apply hQ; rw [TauSOOne.hessian_det_rankOne, h0, mul_zero]
  have hc' : (QFof Q₀).coeff 0 0 ≠ 0 := by simpa [QuadForm.map] using hc
  rw [repMass_rankOne_sq Q₀ hc hs, RankOne.mass_rankOne hc', siegelProductOne_sq Q₀ hQ hs]
  norm_num

/-- **The genus average in rank one at $m = cs^2$:** $r_{\mathrm{gen}}(cs^2) = 2\,\mathcal S_1(cs^2) = 2$. -/
theorem genusAverage_rankOne_sq (Q₀ : QuadForm (𝓞 F) 1) (hQ : Q₀.Nondegenerate) {s : 𝓞 F} (hs : s ≠ 0) :
    repMass (QFof Q₀) (stdLat F 1) (algebraMap (𝓞 F) F (Q₀.coeff 0 0 * s ^ 2)) /
      mass (QFof Q₀) (stdLat F 1) = 2 * siegelProductOne Q₀ (Q₀.coeff 0 0 * s ^ 2) := by
  have hc : Q₀.coeff 0 0 ≠ 0 := by
    intro h0; apply hQ; rw [TauSOOne.hessian_det_rankOne, h0, mul_zero]
  have hc' : (QFof Q₀).coeff 0 0 ≠ 0 := by simpa [QuadForm.map] using hc
  rw [siegelFormulaOne_sq Q₀ hQ hs, RankOne.mass_rankOne hc']
  ring

end Global

/-! ### Over $\mathbb Z$: every $m \ge 1$ -/

section OverZ

open QuadFormsKB.LocalDensity.NF

/-- If some $\beta_p(\langle a\rangle, m)$ vanishes, the corrected product $\mathcal S_1(m)$ is $0$. -/
theorem siegelProductOne_int_eq_zero {a m : ℤ} (ha : a ≠ 0) (hm : m ≠ 0) (h : ∀ k : ℤ, m ≠ a * k ^ 2) :
    siegelProductOne (RatBridge.up (QuadFormsKB.Siegel.RankOne.unary a)) (m : 𝓞 ℚ) = 0 := by
  obtain ⟨p, hp0⟩ := QuadFormsKB.Siegel.RankOne.exists_eulerFactor_eq_zero ha hm h
  set v0 : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) := Rat.HeightOneSpectrum.primesEquiv.symm ⟨p.1, p.2⟩ with hv0def
  have hgen : Rat.HeightOneSpectrum.natGenerator v0 = p.1 := by
    have := congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨p.1, p.2⟩)
    exact this
  have hv0 : NF.localDensity v0 (RatBridge.up (QuadFormsKB.Siegel.RankOne.unary a)) (m : 𝓞 ℚ) / 2 = 0 := by
    have : NF.localDensity v0 (RatBridge.up (QuadFormsKB.Siegel.RankOne.unary a)) (m : 𝓞 ℚ) =
        LocalDensity.localDensity (QuadFormsKB.Siegel.RankOne.unary a) p.1 m := by
      change NF.localDensity v0 ((QuadFormsKB.Siegel.RankOne.unary a).map (Int.castRingHom (𝓞 ℚ))) (m : 𝓞 ℚ) = _
      rw [NF.localDensity_rat, hgen]
    rw [this]
    have h0 := hp0
    unfold QuadFormsKB.Siegel.eulerFactor at h0
    rw [h0]; simp
  have hHas : HasProd (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) =>
      NF.localDensity v (RatBridge.up (QuadFormsKB.Siegel.RankOne.unary a)) (m : 𝓞 ℚ) / 2) 0 := by
    rw [HasProd]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop {v0}] with t ht
    exact (Finset.prod_eq_zero (ht (Finset.mem_singleton_self v0)) hv0).symm
  rw [siegelProductOne, hHas.tprod_eq, mul_zero]

/-- **Siegel's formula in rank one over $\mathbb Z$, every $m \ge 1$ (corrected form).** For $a > 0$ and $m \ge 1$,
$$r_{\mathrm{gen}}(\langle a\rangle, m) = 2\,\mathcal S_1(m),$$
where $\mathcal S_1(m) = \prod_\sigma\frac{\beta_\sigma(m)}2\prod_p\frac{\beta_p(m)}2$ is `siegelProductOne` for $\langle a\rangle\otimes\mathcal O_{\mathbb Q}$:
$\mathcal S_1(m) = 1$ and $r_{\mathrm{gen}} = 2$ when $m = ak^2$ (`siegelProductOne_sq`), and $\mathcal S_1(m) = 0 = r_{\mathrm{gen}}$ otherwise
(a vanishing factor $\beta_p(m)/2$, `Siegel.RankOne.exists_eulerFactor_eq_zero`). -/
@[kb "siegel1935" "Hauptsatz, n = 1 over ℤ, every m (ε = 1/2) [unverified]"]
theorem siegelFormulaOne_int {a m : ℤ} (ha : 0 < a) (hm : 0 < m) :
    QuadFormsKB.Siegel.genusRepAvg (QuadFormsKB.Siegel.RankOne.unary a) m =
      2 * siegelProductOne (RatBridge.up (QuadFormsKB.Siegel.RankOne.unary a)) (m : 𝓞 ℚ) := by
  by_cases hrep : ∃ k : ℤ, m = a * k ^ 2
  · obtain ⟨k, rfl⟩ := hrep
    have hk : k ≠ 0 := by rintro rfl; simp at hm
    have hpd := posDef_unary ha
    have hQ : (RatBridge.up (QuadFormsKB.Siegel.RankOne.unary a)).Nondegenerate := by
      rw [QuadForm.Nondegenerate, TauSOOne.hessian_det_rankOne]
      simp [QuadForm.map, QuadFormsKB.Siegel.RankOne.unary, QuadForm.diag]
      exact ha.ne'
    have hcoef : (RatBridge.up (QuadFormsKB.Siegel.RankOne.unary a)).coeff 0 0 = (a : 𝓞 ℚ) := by
      simp [QuadForm.map, QuadFormsKB.Siegel.RankOne.unary, QuadForm.diag]
    have hs : ((k : ℤ) : 𝓞 ℚ) ≠ 0 := by exact_mod_cast hk
    have h := genusAverage_rankOne_sq (RatBridge.up (QuadFormsKB.Siegel.RankOne.unary a)) hQ hs
    rw [hcoef] at h
    rw [QuadFormsKB.Siegel.genusRepAvg, RatBridge.mass_rat _ hpd, RatBridge.repMass_rat _ hpd]
    have hcast : (((a * k ^ 2 : ℤ)) : 𝓞 ℚ) = (a : 𝓞 ℚ) * ((k : ℤ) : 𝓞 ℚ) ^ 2 := by push_cast; ring
    rw [hcast]
    simpa using h
  · push Not at hrep
    rw [siegelProductOne_int_eq_zero ha.ne' hm.ne' hrep, mul_zero, QuadFormsKB.Siegel.RankOne.genusRepAvg_unary]
    have := QuadFormsKB.Siegel.RankOne.repNum_unary_eq_zero hrep
    exact_mod_cast this

/-- **The rank-one dichotomy, corrected.** For $a > 0$, $m \ge 1$: the literal Euler product of
`Siegel.RankOne.siegel_rank_one_dichotomy` diverges (to $+\infty$) exactly when $m = ak^2$ is represented, while the
corrected formula `siegelFormulaOne_int` holds in both cases, with $\mathcal S_1(m) = 1$, resp. $0$. -/
theorem siegelFormulaOne_int_dichotomy {a m : ℤ} (ha : 0 < a) (hm : 0 < m) :
    QuadFormsKB.Siegel.genusRepAvg (QuadFormsKB.Siegel.RankOne.unary a) m =
        2 * siegelProductOne (RatBridge.up (QuadFormsKB.Siegel.RankOne.unary a)) (m : 𝓞 ℚ) ∧
      (((∃ k : ℤ, m = a * k ^ 2) ∧
          siegelProductOne (RatBridge.up (QuadFormsKB.Siegel.RankOne.unary a)) (m : 𝓞 ℚ) = 1 ∧
          QuadFormsKB.Siegel.genusRepAvg (QuadFormsKB.Siegel.RankOne.unary a) m = 2 ∧
          Filter.Tendsto (QuadFormsKB.Siegel.eulerPartialProd (QuadFormsKB.Siegel.RankOne.unary a) m)
            Filter.atTop Filter.atTop) ∨
        ((∀ k : ℤ, m ≠ a * k ^ 2) ∧
          siegelProductOne (RatBridge.up (QuadFormsKB.Siegel.RankOne.unary a)) (m : 𝓞 ℚ) = 0 ∧
          QuadFormsKB.Siegel.genusRepAvg (QuadFormsKB.Siegel.RankOne.unary a) m = 0 ∧
          HasProd (QuadFormsKB.Siegel.eulerFactor (QuadFormsKB.Siegel.RankOne.unary a) m) 0)) := by
  have hF := siegelFormulaOne_int ha hm
  refine ⟨hF, ?_⟩
  rcases QuadFormsKB.Siegel.RankOne.siegel_rank_one_dichotomy ha.ne' hm.ne' with ⟨hk, hr, ht⟩ | ⟨hk, hr, hP, -⟩
  · have hg : QuadFormsKB.Siegel.genusRepAvg (QuadFormsKB.Siegel.RankOne.unary a) m = 2 := by
      rw [QuadFormsKB.Siegel.RankOne.genusRepAvg_unary, hr]; norm_num
    refine Or.inl ⟨hk, ?_, hg, ht⟩
    rw [hg] at hF
    linarith
  · have hg : QuadFormsKB.Siegel.genusRepAvg (QuadFormsKB.Siegel.RankOne.unary a) m = 0 := by
      rw [QuadFormsKB.Siegel.RankOne.genusRepAvg_unary, hr]; norm_num
    exact Or.inr ⟨hk, siegelProductOne_int_eq_zero ha.ne' hm.ne' hk, hg, hP⟩

end OverZ

end QuadFormsKB.Tamagawa.SiegelRankOne
