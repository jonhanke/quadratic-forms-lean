/-
# Local densities of the hyperbolic plane at every nonzero number

**Layer:** DVR (every residue characteristic, dyadic included) and number field (a finite prime $\mathfrak p$ = `v`).

**Proves** that for the hyperbolic plane $H(x_0, x_1) = x_0 x_1$ and $m = \pi^e u \ne 0$ ($u$ a unit),
$$\beta_\pi(H, m) = (e + 1)\,(1 - q^{-1}),$$
`DVR.localDensity_hyperbolic_pow_mul`, and over a number field
$$\beta_\mathfrak p(H, \langle m\rangle) = (\mathrm{ord}_\mathfrak p(m) + 1)\,(1 - N\mathfrak p^{-1}),$$
`NF.localDensityForm_hyperbolic_unary`. *Proof:* for $k \ge e + 2$ the count is exactly
$r_{\pi^k}(\pi^e u) = (e+1)\,q^{k-1}(q-1)$. For $e \le 1$ there are no Zero-type solutions, and the non-Zero-type
solutions ($x_0$ or $x_1$ a unit mod $\pi^k$; the equation is linear in the other variable) number
$\#(R/\pi^k)^\times$ if $e = 0$ and twice that if $e = 1$. For $e \ge 2$ the Zero-type solutions number
$q^2\, r_{\pi^{k-2}}(\pi^{e-2}u)$ (`repCountZero_eq`) and the non-Zero-type ones again number
$2\,\#(R/\pi^k)^\times$. Here $\#(R/\pi^k)^\times = q^{k-1}(q-1)$, since the non-units form the image of
multiplication by $\pi$ (fibres of size $q$). No hypothesis on $2$ is needed: $H$ is unimodular.
**Depends on** `FormDensityHyperbolic.lean`, `NFFormDensity.lean`.
-/
import QuadFormsKB.LocalDensity.FormDensityHyperbolic
import QuadFormsKB.LocalDensity.NFFormDensity

namespace QuadFormsKB.LocalDensity.DVR

open QuadForm Matrix

set_option linter.unusedSectionVars false
set_option linter.deprecated false

section Counting

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- $H(x) = x_0 x_1$ in any $R$-algebra. -/
theorem evalIn_hyperbolic (S : Type*) [CommRing S] [Algebra R S] (x : Fin 2 → S) :
    (hyperbolic R).evalIn S x = x 0 * x 1 := by
  simp [QuadForm.evalIn, hyperbolic, QuadForm.ofUpper, Fin.sum_univ_two]

/-- **Units of $R/\pi^k$** ($k \ge 1$) are the classes not divisible by $\pi$. -/
theorem isUnit_iff_not_dvd (π : R) (hπ : Irreducible π) (k : ℕ) (hk : 1 ≤ k)
    (z : R ⧸ Ideal.span {π ^ k}) : IsUnit z ↔ ¬ Ideal.Quotient.mk _ π ∣ z := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hdvd : Ideal.Quotient.mk (Ideal.span {π ^ k}) π ∣ Ideal.Quotient.mk _ a ↔ π ∣ a := by
    constructor
    · intro h
      simpa using pow_dvd_of_mk_dvd π k 1 hk a (by simpa using h)
    · exact fun h => map_dvd _ h
  rw [hdvd]
  constructor
  · intro hu hd
    obtain ⟨b, hb⟩ := hd
    have h0 : IsUnit (Ideal.Quotient.mk (Ideal.span {π ^ k}) π) :=
      isUnit_of_dvd_unit ⟨Ideal.Quotient.mk _ b, by rw [← map_mul, ← hb]⟩ hu
    obtain ⟨c, hc⟩ := h0.exists_right_inv
    obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
    have hc' : Ideal.Quotient.mk (Ideal.span {π ^ k}) (π * c') = Ideal.Quotient.mk _ 1 := by
      rw [map_mul, hc, map_one]
    rw [mk_eq_mk_iff] at hc'
    have h1 : π ∣ π * c' - 1 := (dvd_pow_self π (by omega)).trans hc'
    have h2 : π ∣ 1 := by
      have := (dvd_mul_right π c').sub h1
      simpa using this
    exact hπ.not_isUnit (isUnit_of_dvd_one h2)
  · intro h
    exact (dvr_isUnit_of_not_dvd hπ h).map _

variable [Finite (IsLocalRing.ResidueField R)]

/-- The number of units of $R/\pi^k$ is $q^{k-1}(q-1)$. -/
theorem natCard_isUnit_quot (π : R) (hπ : Irreducible π) (k : ℕ) (hk : 1 ≤ k) :
    Nat.card {z : R ⧸ Ideal.span {π ^ k} // IsUnit z} = q R ^ (k - 1) * (q R - 1) := by
  have hfin := finite_quot_pow π hπ k
  have hsplit := natCard_split (α := R ⧸ Ideal.span {π ^ k}) (fun _ => True) (fun z => IsUnit z)
    (fun z => Ideal.Quotient.mk _ π ∣ z) (fun z => IsUnit z) (fun z => by simp)
    (fun z => by simp [isUnit_iff_not_dvd π hπ k hk])
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial)), natCard_quot_pow π hπ] at hsplit
  have hnon : Nat.card {z : R ⧸ Ideal.span {π ^ k} // Ideal.Quotient.mk _ π ∣ z} = q R ^ (k - 1) := by
    have h := natCard_eq_of_fibres
      (fun a : R ⧸ Ideal.span {π ^ k} =>
        (⟨Ideal.Quotient.mk _ π * a, dvd_mul_right _ _⟩ : {z : R ⧸ Ideal.span {π ^ k} //
          Ideal.Quotient.mk _ π ∣ z}))
      (C := Fin (q R)) (fun b => by
        have hc : Nat.card {a : R ⧸ Ideal.span {π ^ k} //
            (⟨Ideal.Quotient.mk _ π * a, dvd_mul_right _ _⟩ : {z : R ⧸ Ideal.span {π ^ k} //
              Ideal.Quotient.mk _ π ∣ z}) = b} = q R := by
          rw [← natCard_mul_pi_fibre π hπ k hk b.1 b.2]
          exact Nat.card_congr (Equiv.subtypeEquivRight fun a => by simp [Subtype.ext_iff])
        have := Finite.of_injective (fun a : {a : R ⧸ Ideal.span {π ^ k} //
            (⟨Ideal.Quotient.mk _ π * a, dvd_mul_right _ _⟩ : {z : R ⧸ Ideal.span {π ^ k} //
              Ideal.Quotient.mk _ π ∣ z}) = b} => a.1) Subtype.val_injective
        exact Finite.equivFinOfCardEq hc)
    rw [natCard_quot_pow π hπ, Nat.card_fin] at h
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hq := q_pos (R := R)
    rw [pow_succ] at h
    simpa using (Nat.eq_of_mul_eq_mul_right hq h).symm
  rw [hnon] at hsplit
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨s, hs⟩ : ∃ s, q R = s + 1 := ⟨q R - 1, by have := q_pos (R := R); omega⟩
  rw [hs, pow_succ] at hsplit
  simp only [Nat.add_sub_cancel, hs] at hsplit ⊢
  nlinarith

section NonZero

variable (π : R) (hπ : Irreducible π) (k : ℕ) (hk : 1 ≤ k)

include hπ hk

/-- A vector with a unit coordinate $x_0$ is not of Zero type. -/
theorem not_allDvd_of_isUnit (f : Fin 2 → R ⧸ Ideal.span {π ^ k}) (h : IsUnit (f 0)) :
    ¬ ∀ i, Ideal.Quotient.mk _ π ∣ f i :=
  fun hd => (isUnit_iff_not_dvd π hπ k hk _).1 h (hd 0)

/-- Solutions of $x_0 x_1 = M$ with $x_0$ a unit correspond to the units $x_0$ ($x_1$ is determined). -/
theorem card_unit_zero (M : R ⧸ Ideal.span {π ^ k}) :
    Nat.card {f : Fin 2 → R ⧸ Ideal.span {π ^ k} // f 0 * f 1 = M ∧ IsUnit (f 0)} =
      Nat.card {z : R ⧸ Ideal.span {π ^ k} // IsUnit z} := by
  refine Nat.card_eq_of_bijective (fun f => ⟨f.1 0, f.2.2⟩) ⟨?_, ?_⟩
  · intro a b h
    have h0 : a.1 0 = b.1 0 := congrArg Subtype.val h
    obtain ⟨f, hf, hu⟩ := a
    obtain ⟨g, hg, hgu⟩ := b
    apply Subtype.ext
    refine funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · exact h0
    · have : f 0 * f 1 = f 0 * g 1 := by
        have h0' : f 0 = g 0 := h0
        rw [hf, h0', hg]
      exact hu.mul_right_inj.1 this
  · rintro ⟨z, hz⟩
    obtain ⟨u, rfl⟩ := hz
    exact ⟨⟨![(u : R ⧸ Ideal.span {π ^ k}), ↑u⁻¹ * M], by simp, by simp⟩, rfl⟩

/-- Solutions of $x_0 x_1 = M$ with $x_1$ a unit correspond to the units $x_1$ ($x_0$ is determined). -/
theorem card_unit_one (M : R ⧸ Ideal.span {π ^ k}) :
    Nat.card {f : Fin 2 → R ⧸ Ideal.span {π ^ k} // f 0 * f 1 = M ∧ IsUnit (f 1)} =
      Nat.card {z : R ⧸ Ideal.span {π ^ k} // IsUnit z} := by
  refine Nat.card_eq_of_bijective (fun f => ⟨f.1 1, f.2.2⟩) ⟨?_, ?_⟩
  · intro a b h
    have h0 : a.1 1 = b.1 1 := congrArg Subtype.val h
    obtain ⟨f, hf, hu⟩ := a
    obtain ⟨g, hg, hgu⟩ := b
    apply Subtype.ext
    refine funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · have : f 0 * f 1 = g 0 * f 1 := by
        have h0' : f 1 = g 1 := h0
        rw [hf, h0', hg]
      exact hu.mul_left_inj.1 this
    · exact h0
  · rintro ⟨z, hz⟩
    obtain ⟨u, rfl⟩ := hz
    refine ⟨⟨![↑u⁻¹ * M, (u : R ⧸ Ideal.span {π ^ k})], ?_, by simp⟩, rfl⟩
    show (↑u⁻¹ * M) * (u : R ⧸ Ideal.span {π ^ k}) = M
    calc (↑u⁻¹ * M) * (u : R ⧸ Ideal.span {π ^ k}) = (↑u⁻¹ * ↑u) * M := by ring
      _ = M := by simp

/-- Non-Zero-type solutions of $x_0 x_1 = M$ with $M$ a unit: $\#(R/\pi^k)^\times$ of them. -/
theorem card_nonZero_of_isUnit (M : R ⧸ Ideal.span {π ^ k}) (hM : IsUnit M) :
    Nat.card {f : Fin 2 → R ⧸ Ideal.span {π ^ k} //
      f 0 * f 1 = M ∧ ¬ ∀ i, Ideal.Quotient.mk _ π ∣ f i} =
      Nat.card {z : R ⧸ Ideal.span {π ^ k} // IsUnit z} := by
  rw [← card_unit_zero π hπ k hk M]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun f => ?_)
  constructor
  · rintro ⟨h1, -⟩
    exact ⟨h1, isUnit_of_mul_isUnit_left (h1 ▸ hM)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, not_allDvd_of_isUnit π hπ k hk f h2⟩

/-- Non-Zero-type solutions of $x_0 x_1 = M$ with $M$ a nonunit: exactly one of $x_0, x_1$ is a unit, so
$2\,\#(R/\pi^k)^\times$ of them. -/
theorem card_nonZero_of_not_isUnit (M : R ⧸ Ideal.span {π ^ k}) (hM : ¬ IsUnit M) :
    Nat.card {f : Fin 2 → R ⧸ Ideal.span {π ^ k} //
      f 0 * f 1 = M ∧ ¬ ∀ i, Ideal.Quotient.mk _ π ∣ f i} =
      2 * Nat.card {z : R ⧸ Ideal.span {π ^ k} // IsUnit z} := by
  have hfin := finite_quot_pow π hπ k
  have hsplit := natCard_split (α := Fin 2 → R ⧸ Ideal.span {π ^ k})
    (fun f => f 0 * f 1 = M ∧ ¬ ∀ i, Ideal.Quotient.mk _ π ∣ f i)
    (fun f => (f 0 * f 1 = M ∧ ¬ ∀ i, Ideal.Quotient.mk _ π ∣ f i) ∧ IsUnit (f 0))
    (fun f => (f 0 * f 1 = M ∧ ¬ ∀ i, Ideal.Quotient.mk _ π ∣ f i) ∧ ¬ IsUnit (f 0))
    (fun f => IsUnit (f 0)) (fun f => Iff.rfl) (fun f => Iff.rfl)
  rw [hsplit, two_mul]
  congr 1
  · rw [← card_unit_zero π hπ k hk M]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun f => ?_)
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, not_allDvd_of_isUnit π hπ k hk f h2⟩, h2⟩
  · rw [← card_unit_one π hπ k hk M]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun f => ?_)
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, ?_⟩
      by_contra h4
      apply h2
      intro i
      fin_cases i
      · exact not_not.1 (fun h => h3 ((isUnit_iff_not_dvd π hπ k hk _).2 h))
      · exact not_not.1 (fun h => h4 ((isUnit_iff_not_dvd π hπ k hk _).2 h))
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, ?_⟩, ?_⟩
      · intro hd
        exact (isUnit_iff_not_dvd π hπ k hk _).1 h2 (hd 1)
      · intro h3
        exact hM (h1 ▸ h3.mul h2)

end NonZero

section Recursion

variable (π : R) (hπ : Irreducible π)

include hπ

open Classical in
/-- **Non-Zero-type count** of $x_0 x_1 \equiv m \pmod{\pi^k}$: $\#(R/\pi^k)^\times$ if $m$ is a unit, twice that
otherwise. -/
theorem repCountOf_nonZero_hyperbolic (k : ℕ) (hk : 1 ≤ k) (m : R) :
    repCountOf (hyperbolic R) π k m (fun x => ¬ IsZeroType π k x) =
      (if IsUnit m then 1 else 2) * (q R ^ (k - 1) * (q R - 1)) := by
  have hfin := finite_quot_pow π hπ k
  rw [← natCard_isUnit_quot π hπ k hk]
  have hc : repCountOf (hyperbolic R) π k m (fun x => ¬ IsZeroType π k x) =
      Nat.card {f : Fin 2 → R ⧸ Ideal.span {π ^ k} //
        f 0 * f 1 = Ideal.Quotient.mk _ m ∧ ¬ ∀ i, Ideal.Quotient.mk _ π ∣ f i} := by
    unfold repCountOf
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [evalIn_hyperbolic]; rfl)
  rw [hc]
  by_cases hm : IsUnit m
  · rw [if_pos hm, one_mul]
    exact card_nonZero_of_isUnit π hπ k hk _ (hm.map _)
  · rw [if_neg hm]
    refine card_nonZero_of_not_isUnit π hπ k hk _ ?_
    rw [isUnit_iff_not_dvd π hπ k hk, not_not]
    exact map_dvd _ (by by_contra h; exact hm (dvr_isUnit_of_not_dvd hπ h))

/-- No Zero-type solutions of $x_0 x_1 \equiv m$ when $\pi^2 \nmid m$. -/
theorem repCountOf_zero_hyperbolic_eq_zero (k : ℕ) (hk : 2 ≤ k) (m : R) (hm : ¬ π ^ 2 ∣ m) :
    repCountOf (hyperbolic R) π k m (IsZeroType π k) = 0 := by
  unfold repCountOf
  rw [Nat.card_eq_zero]; left
  refine ⟨fun ⟨x, hx, hz⟩ => ?_⟩
  rw [evalIn_hyperbolic] at hx
  obtain ⟨a, ha⟩ := hz 0
  obtain ⟨b, hb⟩ := hz 1
  exact hm (pow_dvd_of_mk_dvd π k 2 hk m ⟨a * b, by rw [← hx, ha, hb]; ring⟩)

/-- **Exact count** $r_{\pi^k}(\pi^e u) = (e+1)\,q^{k-1}(q-1)$ for $k \ge e + 2$ (induction on $e$ in steps of 2
via the Zero-type reduction `repCountZero_eq`). -/
theorem repCount_hyperbolic_pow_mul (u : R) (hu : IsUnit u) :
    ∀ e k : ℕ, e + 2 ≤ k →
      repCount (hyperbolic R) π k (π ^ e * u) = (e + 1) * (q R ^ (k - 1) * (q R - 1)) := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
  intro k hk
  rw [repCount_eq_zero_add_nonZero (hyperbolic R) π hπ k (π ^ e * u),
    repCountOf_nonZero_hyperbolic π hπ k (by omega)]
  rcases e with _ | _ | e
  · rw [repCountOf_zero_hyperbolic_eq_zero π hπ k (by omega) _ (by
      intro h
      exact dvr_not_pow_succ_dvd hπ hu 0 ((pow_dvd_pow π (by omega)).trans h))]
    simp [hu]
  · rw [repCountOf_zero_hyperbolic_eq_zero π hπ k (by omega) _ (by
      intro h
      exact dvr_not_pow_succ_dvd hπ hu 1 ((pow_dvd_pow π (by omega)).trans h))]
    have : ¬ IsUnit (π ^ (0 + 1) * u) := fun h =>
      hπ.not_isUnit (isUnit_of_dvd_unit (by simp) h)
    simp only [this, if_false]
    ring
  · have hnu : ¬ IsUnit (π ^ (e + 1 + 1) * u) := fun h =>
      hπ.not_isUnit (isUnit_of_dvd_unit
        (dvd_mul_of_dvd_left (dvd_pow_self π (by omega)) u) h)
    rw [if_neg hnu, repCountZero_eq (hyperbolic R) π hπ _ (π ^ e * u) (by ring) k (by omega),
      ih e (by omega) (k - 2) (by omega)]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    have e1 : j + 3 - 2 = j + 1 := rfl
    have e2 : j + 3 - 1 = j + 2 := rfl
    rw [e1, e2, Nat.add_sub_cancel]
    ring

end Recursion

/-- The hyperbolic plane commutes with change of coefficient ring. -/
theorem hyperbolic_map_ring {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) :
    (hyperbolic A).map f = hyperbolic B := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hyperbolic, QuadForm.map, QuadForm.ofUpper]

/-- **The local density of the hyperbolic plane at $\pi^e u$** ($u$ a unit): $\beta_\pi(H, \pi^e u) = (e+1)(1 - q^{-1})$,
at every prime, dyadic included [closed form: unverified against the literature; proved here]. -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
theorem localDensity_hyperbolic_pow_mul (π : R) (hπ : Irreducible π) (u : R) (hu : IsUnit u)
    (e : ℕ) :
    localDensity (hyperbolic R) π (π ^ e * u) = ((e : ℝ) + 1) * (1 - 1 / (q R : ℝ)) := by
  have hq : (0 : ℝ) < q R := by exact_mod_cast q_pos (R := R)
  unfold localDensity
  apply Filter.Tendsto.limUnder_eq
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (e + 2)] with k hk
  rw [repCount_hyperbolic_pow_mul π hπ u hu e k hk]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h1 : 1 ≤ q R := q_pos
  push_cast [Nat.cast_sub h1]
  simp only [mul_one]
  field_simp
  ring

end Counting

end QuadFormsKB.LocalDensity.DVR

/-! ### Number fields -/

namespace QuadFormsKB.LocalDensity.NF

open NumberField IsDedekindDomain

variable {F : Type*} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

/-- $m \in \mathfrak p^c \setminus \mathfrak p^{c+1}$ for $m \ne 0$, where $c = \mathrm{ord}_\mathfrak p(m)$ is the
multiplicity of $\mathfrak p$ in $(m)$. -/
theorem mem_pow_count {m : 𝓞 F} (hm : m ≠ 0) :
    m ∈ v.asIdeal ^ (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {m})).factors ∧
      m ∉ v.asIdeal ^ ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {m})).factors + 1) := by
  have hv := v.intValuation_if_neg hm
  refine ⟨(v.intValuation_le_pow_iff_mem m _).1 (by rw [hv]), fun h => ?_⟩
  have := (v.intValuation_le_pow_iff_mem m _).2 h
  rw [hv, WithZero.exp_le_exp] at this
  change -(((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {m})).factors : ℕ) : ℤ) ≤
    -((((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {m})).factors + 1 : ℕ)) : ℤ) at this
  push_cast at this; omega

/-- **$\iota(m) = \varpi^{\mathrm{ord}_\mathfrak p(m)}\cdot u$ with $u$ a unit of $\mathfrak o_\mathfrak p$** for
$m \ne 0$ (the exponent is the multiplicity of $\mathfrak p$ in $(m)$). -/
theorem ι_eq_π_pow_mul_unit {m : 𝓞 F} (hm : m ≠ 0) :
    ∃ u : v.adicCompletionIntegers F, IsUnit u ∧
      ι v m = π v ^ (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {m})).factors * u := by
  obtain ⟨h1, h2⟩ := mem_pow_count v hm
  obtain ⟨u, hu, hu'⟩ := DVR.dvr_exact (irreducible_π v) ((π_pow_dvd_ι_iff v _ m).2 h1)
    (fun h => h2 ((π_pow_dvd_ι_iff v _ m).1 h))
  exact ⟨u, hu', hu⟩

/-- **The density of $H = x_0x_1$ at a nonzero number at every finite prime:**
$$\beta_\mathfrak p(H, \langle m\rangle) = (\mathrm{ord}_\mathfrak p(m) + 1)(1 - N\mathfrak p^{-1}),$$
where $\mathrm{ord}_\mathfrak p(m)$ is the multiplicity of $\mathfrak p$ in $(m)$. Every prime, dyadic included. -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
theorem localDensityForm_hyperbolic_unary (v : HeightOneSpectrum (𝓞 F)) (m : 𝓞 F) (hm : m ≠ 0) :
    localDensityForm v (DVR.hyperbolic (𝓞 F)) (DVR.unary m) =
      (((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {m})).factors : ℕ) + 1 : ℝ) *
        (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹) := by
  obtain ⟨u, hu, hι⟩ := ι_eq_π_pow_mul_unit v hm
  rw [localDensityForm_unary, localDensity_eq_completion,
    show Qp v (DVR.hyperbolic (𝓞 F)) = DVR.hyperbolic (v.adicCompletionIntegers F) from
      DVR.hyperbolic_map_ring _,
    hι, DVR.localDensity_hyperbolic_pow_mul (π v) (irreducible_π v) u hu, q_completion, one_div]

end QuadFormsKB.LocalDensity.NF
