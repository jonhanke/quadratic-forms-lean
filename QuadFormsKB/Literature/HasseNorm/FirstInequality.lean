/-
# Hasse norm theorem, step 3: the global norm index of `S`-units

For a quadratic extension $L/F$ of number fields with nontrivial automorphism $\sigma$ and a finite set
$S$ of primes of $F$ ($S_L$ = `overS S`, the primes of $L$ above $S$):

* `σS`: $\sigma$ acting on $L_{S_L}^\times$ (via $w(\sigma x) = (\sigma^{-1}w)(x)$, `valuation_galois`);
* `range_inclS`: the $\sigma$-fixed $S_L$-units are exactly $F_S^\times$;
* `over_eq_or`: primes of $L$ over the same prime of $F$ are equal or $\sigma$-conjugate;
* `hilbert90`, `herbrandM1_eq_one`: Hilbert 90 for $S$-units, $h^{-1}(L_{S_L}^\times) = 1$ when $S$ contains the
  ramified primes and $\mathrm{Cl}_S(F) = 1$;
* `index_normsF_mul`: $[F_S^\times : N L_{S_L}^\times]\cdot 2^{\operatorname{rk} L_{S_L}^\times} = 2^{2\operatorname{rk} F_S^\times}$.

Together with the count of places of $L$ over $S$ (next step) this is Milne VII §3 + Lemma 4.5 in
$S$-unit form: $[F_S^\times : N L_{S_L}^\times] = 2^{s'-1}$. See `Herbrand.lean` for the overall plan.
Locators are from memory and still `[unverified]`.
-/
import QuadFormsKB.Literature.HasseNorm.SUnits

open Module NumberField IsDedekindDomain WithZero
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.HN

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- **The prime $e^{-1}(\mathfrak w)$** for a ring automorphism $e$ of a Dedekind domain. -/
def comapEquiv (e : R ≃+* R) (w : HeightOneSpectrum R) : HeightOneSpectrum R where
  asIdeal := w.asIdeal.comap e
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    apply w.ne_bot
    have := congrArg (Ideal.map e) h
    rw [Ideal.map_comap_of_surjective _ e.surjective, Ideal.map_bot] at this
    exact this

omit [IsDedekindDomain R] in
@[simp] lemma comapEquiv_asIdeal (e : R ≃+* R) (w : HeightOneSpectrum R) :
    (comapEquiv e w).asIdeal = w.asIdeal.comap e := rfl

omit [IsDedekindDomain R] in
lemma comap_pow_equiv (e : R ≃+* R) (I : Ideal R) (n : ℕ) :
    (I ^ n).comap e = (I.comap e) ^ n := by
  rw [← Ideal.map_symm, ← Ideal.map_symm, Ideal.map_pow]

theorem intValuation_comapEquiv (e : R ≃+* R) (w : HeightOneSpectrum R) (r : R) :
    (comapEquiv e w).intValuation r = w.intValuation (e r) := by
  by_cases hr : r = 0
  · subst hr; simp
  have her : e r ≠ 0 := by simpa using hr
  have key : ∀ n : ℕ, (comapEquiv e w).intValuation r ≤ exp (-(n : ℤ)) ↔
      w.intValuation (e r) ≤ exp (-(n : ℤ)) := by
    intro n
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem,
      comapEquiv_asIdeal, ← comap_pow_equiv, Ideal.mem_comap]
  rw [HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hr,
    HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ her] at key ⊢
  set m₁ := multiplicity (comapEquiv e w).asIdeal (Ideal.span {r})
  set m₂ := multiplicity w.asIdeal (Ideal.span {e r})
  have h1 := (key m₁).mp le_rfl
  have h2 := (key m₂).mpr le_rfl
  rw [exp_le_exp, neg_le_neg_iff, Nat.cast_le] at h1 h2
  rw [le_antisymm h2 h1]


section NF

variable {L : Type*} [Field L] [NumberField L]

/-- For a field automorphism `τ` of a number field, `w(τ x) = (τ⁻¹ w)(x)`. -/
theorem valuation_comapEquiv (τ : L ≃+* L) (w : HeightOneSpectrum (𝓞 L)) (x : L) :
    (comapEquiv (RingOfIntegers.mapRingEquiv τ) w).valuation L x = w.valuation L (τ x) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) x
  rw [map_div₀, map_div₀, map_div₀]
  have h : ∀ c : 𝓞 L, τ (algebraMap (𝓞 L) L c) =
      algebraMap (𝓞 L) L (RingOfIntegers.mapRingEquiv τ c) := fun c => rfl
  rw [h, h, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    intValuation_comapEquiv, intValuation_comapEquiv]

end NF

section General

variable {K : Type*} [Field K] [NumberField K]

/-- A nonzero element has valuation `1` at all but finitely many primes. -/
lemma finite_support (y : Kˣ) :
    {w : HeightOneSpectrum (𝓞 K) | w.valuationOfNeZero y ≠ 1}.Finite := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 K) (y : K)
  have ha : a ≠ 0 := by
    rintro rfl; simp at hab; exact y.ne_zero hab.symm
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have fin : ∀ c : 𝓞 K, c ≠ 0 → {w : HeightOneSpectrum (𝓞 K) | c ∈ w.asIdeal}.Finite := by
    intro c hc
    refine (Ideal.finite_factors (I := Ideal.span {c}) (by simpa using hc)).subset ?_
    intro w hw
    rw [Set.mem_ofPred_eq, Ideal.dvd_span_singleton]; exact hw
  refine ((fin a ha).union (fin b hb0)).subset ?_
  intro w hw
  by_contra hc
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at hc
  apply hw
  rw [← WithZero.coe_inj, HeightOneSpectrum.valuationOfNeZero_eq, ← hab, map_div₀,
    (HeightOneSpectrum.valuation_eq_one_iff_notMem w).mpr hc.1,
    (HeightOneSpectrum.valuation_eq_one_iff_notMem w).mpr hc.2, div_one]
  rfl

/-- An element of `𝔭 \ 𝔭²` has valuation `exp(-1)` at `𝔭`. -/
lemma valuation_of_mem_not_sq (p : HeightOneSpectrum (𝓞 K)) {c : 𝓞 K} (hc : c ∈ p.asIdeal)
    (hc2 : c ∉ p.asIdeal ^ 2) : p.valuation K (algebraMap (𝓞 K) K c) = exp (-1 : ℤ) := by
  have hc0 : c ≠ 0 := by rintro rfl; exact hc2 (zero_mem _)
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  have h1 : p.intValuation c ≤ exp (-((1 : ℕ) : ℤ)) := by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, pow_one]; exact hc
  have h2 : ¬ p.intValuation c ≤ exp (-((2 : ℕ) : ℤ)) := by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]; exact hc2
  rw [HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hc0] at h1 h2 ⊢
  rw [exp_le_exp, neg_le_neg_iff, Nat.cast_le] at h1 h2
  rw [show multiplicity p.asIdeal (Ideal.span {c}) = 1 by omega]
  rfl

end General

section Quadratic

variable {F L : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
  [Algebra.IsQuadraticExtension F L]

/-- The prime of `F` below a prime `w` of `L`. -/
def under (w : HeightOneSpectrum (𝓞 L)) : HeightOneSpectrum (𝓞 F) where
  asIdeal := w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 L))
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := Ideal.IsIntegral.under_ne_bot (𝓞 F) w.ne_bot

omit [Algebra.IsQuadraticExtension F L] in
@[simp] lemma under_asIdeal (w : HeightOneSpectrum (𝓞 L)) :
    (under (F := F) w).asIdeal = w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 L)) := rfl

instance (w : HeightOneSpectrum (𝓞 L)) : w.asIdeal.LiesOver (under (F := F) w).asIdeal :=
  ⟨rfl⟩

variable (σ : L ≃ₐ[F] L)

/-- The automorphism of `𝓞 L` induced by `σ`. -/
abbrev σO : 𝓞 L ≃+* 𝓞 L := RingOfIntegers.mapRingEquiv (σ : L ≃+* L)

omit [Algebra.IsQuadraticExtension F L] in
lemma under_comapEquiv (w : HeightOneSpectrum (𝓞 L)) :
    under (F := F) (comapEquiv (σO σ) w) = under w := by
  ext x
  simp only [under_asIdeal, comapEquiv_asIdeal, Ideal.mem_comap]
  have : (σO σ) (algebraMap (𝓞 F) (𝓞 L) x) = algebraMap (𝓞 F) (𝓞 L) x := by
    apply RingOfIntegers.ext
    have e : ((algebraMap (𝓞 F) (𝓞 L) x : 𝓞 L) : L) = algebraMap F L (x : F) := rfl
    simp only [RingOfIntegers.mapRingEquiv_apply]
    rw [e]
    exact σ.commutes (x : F)
  rw [this]


/-- The primes of `L` above a finite set `S` of primes of `F`. -/
def overS (S : Finset (HeightOneSpectrum (𝓞 F))) : Finset (HeightOneSpectrum (𝓞 L)) :=
  Set.Finite.toFinset (s := {w : HeightOneSpectrum (𝓞 L) | under (F := F) w ∈ S}) (by
    classical
    have : {w : HeightOneSpectrum (𝓞 L) | under (F := F) w ∈ S} ⊆
        ⋃ p ∈ S, {w : HeightOneSpectrum (𝓞 L) | w.asIdeal ∣ p.asIdeal.map (algebraMap (𝓞 F) (𝓞 L))} := by
      intro w hw
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
      refine ⟨under w, hw, ?_⟩
      rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap]
      exact le_rfl
    refine Set.Finite.subset (Set.Finite.biUnion S.finite_toSet fun p _ => ?_) this
    apply Ideal.finite_factors
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 L))]
    exact p.ne_bot)

lemma mem_overS {S : Finset (HeightOneSpectrum (𝓞 F))} {w : HeightOneSpectrum (𝓞 L)} :
    w ∈ overS S ↔ under (F := F) w ∈ S := by
  simp [overS]

lemma valuation_galois (w : HeightOneSpectrum (𝓞 L)) (x : L) :
    w.valuation L (σ x) = (comapEquiv (σO σ) w).valuation L x :=
  (valuation_comapEquiv (σ : L ≃+* L) w x).symm

/-- `σ` acting on the `S_L`-units (additive notation), `S_L = overS S`. -/
def σS (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Additive (SUnit (F := L) (overS (L := L) S)) →+ Additive (SUnit (F := L) (overS (L := L) S)) where
  toFun x := Additive.ofMul ⟨Units.map (σ : L →* L) (Additive.toMul x : SUnit _), by
    intro w hw
    have hw' : comapEquiv (σO σ) w ∉ (overS (L := L) S : Set _) := by
      simp only [Finset.mem_coe, mem_overS, under_comapEquiv] at hw ⊢; exact hw
    simp only [Units.coe_map, MonoidHom.coe_ofClass]
    rw [valuation_galois]
    exact (Additive.toMul x).2 _ hw'⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

@[simp] lemma σS_apply (S : Finset (HeightOneSpectrum (𝓞 F)))
    (x : Additive (SUnit (F := L) (overS (L := L) S))) :
    (((Additive.toMul (σS σ S x) : SUnit _) : Lˣ) : L) = σ (((Additive.toMul x : SUnit _) : Lˣ) : L) :=
  rfl


/-- Every element of the Galois group of a quadratic extension squares to `1`. -/
lemma mul_self_eq_one : σ * σ = 1 := by
  have hcard : Nat.card (L ≃ₐ[F] L) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]
  have := pow_card_eq_one' (G := L ≃ₐ[F] L) (x := σ)
  rw [hcard, pow_two] at this
  exact this

lemma apply_apply (x : L) : σ (σ x) = x := by
  have := congrArg (fun τ : L ≃ₐ[F] L => τ x) (mul_self_eq_one σ)
  simpa using this

/-- **The fixed field of the nontrivial automorphism is `F`.** -/
lemma fixed_iff (hσ : σ ≠ 1) (x : L) : σ x = x ↔ x ∈ (algebraMap F L).range := by
  have hz : Subgroup.zpowers σ = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ ?_
    have ho : orderOf σ = 2 := orderOf_eq_prime_iff.mpr ⟨by rw [pow_two]; exact mul_self_eq_one σ, hσ⟩
    rw [Nat.card_zpowers, ho, IsGalois.card_aut_eq_finrank,
      Algebra.IsQuadraticExtension.finrank_eq_two]
  convert (IntermediateField.mem_fixedField_iff (⊤ : Subgroup (L ≃ₐ[F] L)) x).symm using 1
  · rw [← hz, Subgroup.forall_mem_zpowers]
    exact (MulAction.mem_fixedBy_zpowers_iff_mem_fixedBy (g := σ)).symm
  · rw [IsGalois.fixedField_top, IntermediateField.mem_bot]
    rfl

lemma eq_one_of_pow_eq_one {a : ℤᵐ⁰} {n : ℕ} (hn : n ≠ 0) (h : a ^ n = 1) : a = 1 := by
  induction a using WithZero.recZeroCoe with
  | zero => rw [zero_pow hn] at h; exact absurd h zero_ne_one
  | coe b =>
    rw [← WithZero.coe_pow, ← WithZero.coe_one, WithZero.coe_inj] at h
    rw [← WithZero.coe_one, WithZero.coe_inj]
    exact (pow_eq_one_iff_left hn).mp h

lemma valuation_algebraMap (w : HeightOneSpectrum (𝓞 L)) (c : F) :
    w.valuation L (algebraMap F L c) =
      (under (F := F) w).valuation F c ^ w.asIdeal.ramificationIdx (𝓞 F) :=
  (HeightOneSpectrum.valuation_liesOver L (under (F := F) w) w c).symm

lemma ramificationIdx_ne_zero (w : HeightOneSpectrum (𝓞 L)) :
    w.asIdeal.ramificationIdx (𝓞 F) ≠ 0 :=
  (Ideal.ramificationIdx_pos_of_isDedekindDomain' w.asIdeal (under (F := F) w).ne_bot).ne'


omit [Algebra.IsQuadraticExtension F L] in
/-- Every prime of `F` has a prime of `L` above it. -/
lemma exists_over (p : HeightOneSpectrum (𝓞 F)) : ∃ w : HeightOneSpectrum (𝓞 L), under w = p := by
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) p.asIdeal
  have hQ0 : Q ≠ ⊥ := by
    intro h
    apply p.ne_bot
    rw [hQ.over, h, Ideal.under_def, Ideal.comap_bot_of_injective _
      (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 L))]
  refine ⟨⟨Q, hQmax.isPrime, hQ0⟩, ?_⟩
  ext1
  exact hQ.over.symm

/-- `F_S → L_{S_L}`, `c ↦ c` (additive notation). -/
def inclS (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Additive (SUnit (F := F) S) →+ Additive (SUnit (F := L) (overS (L := L) S)) where
  toFun c := Additive.ofMul ⟨Units.map (algebraMap F L : F →* L) (Additive.toMul c : SUnit _), by
    intro w hw
    have hw' : under (F := F) w ∉ (S : Set _) := by
      simpa [mem_overS] using hw
    simp only [Units.coe_map, MonoidHom.coe_ofClass]
    rw [valuation_algebraMap, (Additive.toMul c).2 _ hw', one_pow]⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

@[simp] lemma inclS_apply (S : Finset (HeightOneSpectrum (𝓞 F))) (c : Additive (SUnit (F := F) S)) :
    (((Additive.toMul (inclS (L := L) S c) : SUnit _) : Lˣ) : L) =
      algebraMap F L (((Additive.toMul c : SUnit _) : Fˣ) : F) := rfl

lemma inclS_injective (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Function.Injective (inclS (L := L) S) := by
  intro x y h
  have := congrArg (fun z => (((Additive.toMul z : SUnit _) : Lˣ) : L)) h
  simp only [inclS_apply] at this
  apply Additive.toMul.injective; apply Subtype.ext; apply Units.ext
  exact (algebraMap F L).injective this

/-- **The `σ`-fixed `S_L`-units are the `S`-units of `F`.** -/
lemma range_inclS (hσ : σ ≠ 1) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    (inclS (L := L) S).range = (diffHom (σS σ S)).ker := by
  ext x
  rw [mem_fixed]
  constructor
  · rintro ⟨c, rfl⟩
    apply Additive.toMul.injective; apply Subtype.ext; apply Units.ext
    show σ (algebraMap F L _) = algebraMap F L _
    exact σ.commutes _
  · intro hx
    have hx' : σ (((Additive.toMul x : SUnit _) : Lˣ) : L) = (((Additive.toMul x : SUnit _) : Lˣ) : L) := by
      have := congrArg (fun z => (((Additive.toMul z : SUnit _) : Lˣ) : L)) hx
      simpa using this
    obtain ⟨c, hc⟩ := (fixed_iff σ hσ _).mp hx'
    have hc0 : c ≠ 0 := by
      rintro rfl; simp only [map_zero] at hc; exact (Units.ne_zero _) hc.symm
    refine ⟨Additive.ofMul ⟨Units.mk0 c hc0, ?_⟩, ?_⟩
    · intro p hp
      obtain ⟨w, rfl⟩ := exists_over (L := L) p
      have hw' : w ∉ (overS (L := L) S : Set _) := by simpa [mem_overS] using hp
      have h1 := (Additive.toMul x).2 w hw'
      rw [← hc, valuation_algebraMap] at h1
      exact eq_one_of_pow_eq_one (ramificationIdx_ne_zero (F := F) w) h1
    · apply Additive.toMul.injective; apply Subtype.ext; apply Units.ext
      simp [hc]


open Pointwise in
/-- **Two primes of `L` over the same prime of `F` are equal or `σ`-conjugate.** -/
lemma over_eq_or (hσ : σ ≠ 1) (w w' : HeightOneSpectrum (𝓞 L))
    (h : under (F := F) w = under w') : w' = w ∨ w' = comapEquiv (σO σ) w := by
  classical
  have hinv : Algebra.IsInvariant (𝓞 F) (𝓞 L) (𝓞 L ≃ₐ[𝓞 F] 𝓞 L) :=
    Algebra.isInvariant_of_isGalois' (𝓞 F) F L (𝓞 L)
  have hfin : Finite (𝓞 L ≃ₐ[𝓞 F] 𝓞 L) :=
    Finite.of_equiv _ (galRestrict (𝓞 F) F L (𝓞 L)).toEquiv
  have hu : w.asIdeal.under (𝓞 F) = w'.asIdeal.under (𝓞 F) := congrArg HeightOneSpectrum.asIdeal h
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 F) (𝓞 L)
    (𝓞 L ≃ₐ[𝓞 F] 𝓞 L) w.asIdeal w'.asIdeal hu
  set τ := (galRestrict (𝓞 F) F L (𝓞 L)).symm g with hτ
  have hgτ : g = galRestrict (𝓞 F) F L (𝓞 L) τ := by simp [hτ]
  have hτ2 : τ = 1 ∨ τ = σ := by
    by_contra hc
    push Not at hc
    have hcard : Nat.card (L ≃ₐ[F] L) = 2 := by
      rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]
    have h3 : ({1, σ, τ} : Finset (L ≃ₐ[F] L)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair hc.2.symm]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hσ.symm, hc.1.symm⟩
    have := Finset.card_le_univ ({1, σ, τ} : Finset (L ≃ₐ[F] L))
    rw [h3, Fintype.card_eq_nat_card, hcard] at this
    omega
  rcases hτ2 with h1 | h1
  · left
    ext1
    rw [hg, hgτ, h1, map_one, one_smul]
  · right
    ext1
    rw [hg, hgτ, h1, Ideal.pointwise_smul_def, comapEquiv_asIdeal]
    set g' := galRestrict (𝓞 F) F L (𝓞 L) σ with hg'
    have hgg : g' * g' = 1 := by rw [hg', ← map_mul, mul_self_eq_one, map_one]
    have hsymm : g'.symm = g' := by
      have : g'⁻¹ = g' := inv_eq_of_mul_eq_one_left hgg
      exact this
    have hval : ∀ y : 𝓞 L, g' y = σO σ y := by
      intro y
      apply RingOfIntegers.ext
      exact algebraMap_galRestrict_apply (𝓞 F) σ y
    change Ideal.map (g' : 𝓞 L →+* 𝓞 L) w.asIdeal = _
    change Ideal.map ((g' : 𝓞 L ≃+* 𝓞 L) : 𝓞 L →+* 𝓞 L) w.asIdeal = _
    rw [Ideal.map_comap_of_equiv]
    ext y
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have : g'.toRingEquiv.symm y = σO σ y := by
      rw [show g'.toRingEquiv.symm y = g'.symm y from rfl, hsymm]; exact hval y
    rw [this]


/-- **Hilbert 90 for a quadratic extension**, explicitly: if $x\,\sigma(x) = 1$ then $x = y/\sigma(y)$ with
$y = 1 + x$ (or $y = s - \sigma s$ for any $s \notin F$ when $x = -1$). -/
lemma hilbert90 (hσ : σ ≠ 1) (x : Lˣ) (hx : (x : L) * σ x = 1) :
    ∃ y : Lˣ, (x : L) = y / σ y := by
  by_cases hm : (x : L) = -1
  · obtain ⟨s, hs⟩ : ∃ s : L, s ∉ (algebraMap F L).range := by
      by_contra hc
      push Not at hc
      apply hσ
      ext z
      obtain ⟨c, rfl⟩ := hc z
      simp
    have hy : s - σ s ≠ 0 := by
      intro h0
      apply hs
      exact (fixed_iff σ hσ s).mp (by rw [sub_eq_zero] at h0; exact h0.symm)
    refine ⟨Units.mk0 _ hy, ?_⟩
    have hσy : σ (s - σ s) = -(s - σ s) := by rw [map_sub, apply_apply]; ring
    simp only [Units.val_mk0]
    rw [hσy, div_neg, div_self hy, hm]
  · have hx0 : (x : L) ≠ 0 := x.ne_zero
    have hy : 1 + (x : L) ≠ 0 := by
      intro h; apply hm; linear_combination h
    refine ⟨Units.mk0 _ hy, ?_⟩
    simp only [Units.val_mk0]
    have hσx : σ (x : L) = (x : L)⁻¹ := by
      exact eq_inv_of_mul_eq_one_right hx
    rw [map_add, map_one, hσx]
    have hden : 1 + (x : L)⁻¹ ≠ 0 := by
      intro h; apply hy
      have : (x : L) * (1 + (x : L)⁻¹) = 1 + x := by field_simp; ring
      rw [← this, h, mul_zero]
    rw [eq_div_iff hden, mul_add, mul_one, mul_inv_cancel₀ hx0, add_comm]

/-- `x ∈ F_S` iff its valuation (in `Multiplicative ℤ`) is `1` outside `S`. -/
lemma mem_sUnit_iff {K : Type*} [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : Kˣ) : x ∈ SUnit (F := K) S ↔ ∀ w ∉ S, w.valuationOfNeZero x = 1 := by
  constructor
  · intro h w hw
    have := h w (by simpa using hw)
    rw [← HeightOneSpectrum.valuationOfNeZero_eq] at this
    exact_mod_cast this
  · intro h w hw
    rw [← HeightOneSpectrum.valuationOfNeZero_eq, h w (by simpa using hw)]
    rfl

lemma valuationOfNeZero_galois (w : HeightOneSpectrum (𝓞 L)) (y : Lˣ) :
    w.valuationOfNeZero (Units.map (σ : L →* L) y) =
      (comapEquiv (σO σ) w).valuationOfNeZero y := by
  have := valuation_galois σ w (y : L)
  rw [← HeightOneSpectrum.valuationOfNeZero_eq] at this
  rw [← WithZero.coe_inj, HeightOneSpectrum.valuationOfNeZero_eq,
    HeightOneSpectrum.valuationOfNeZero_eq]
  exact valuation_galois σ w (y : L)

lemma valuationOfNeZero_algebraMap (w : HeightOneSpectrum (𝓞 L)) (c : Fˣ) :
    w.valuationOfNeZero (Units.map (algebraMap F L : F →* L) c) =
      (under (F := F) w).valuationOfNeZero c ^ w.asIdeal.ramificationIdx (𝓞 F) := by
  rw [← WithZero.coe_inj, WithZero.coe_pow, HeightOneSpectrum.valuationOfNeZero_eq,
    HeightOneSpectrum.valuationOfNeZero_eq]
  exact valuation_algebraMap w (c : F)


/-- Coordinates of the `σS` action in `L`. -/
lemma toMul_σS_val (S : Finset (HeightOneSpectrum (𝓞 F)))
    (x : Additive (SUnit (F := L) (overS (L := L) S))) :
    (((Additive.toMul (σS σ S x) : SUnit _) : Lˣ)) = Units.map (σ : L →* L) (Additive.toMul x : SUnit _) :=
  rfl

/-- **Hilbert 90 for `S`-units: $h^{-1}(L_S^\times) = 1$** when $S$ contains the primes ramified in $L$
(`hram`) and $S$-uniformizers exist outside $S$ (`hS`, i.e. $\mathrm{Cl}_S(F) = 1$): every $S_L$-unit $x$
with $x\,\sigma(x) = 1$ is $y/\sigma(y)$ for an $S_L$-unit $y$.

*Proof.* Hilbert 90 (`hilbert90`) gives $y_0 \in L^\times$ with $x = y_0/\sigma y_0$. Outside $S_L$ the
valuations of $y_0$ are $\sigma$-invariant, hence (primes over $\mathfrak p$ are $\sigma$-conjugate,
`over_eq_or`) depend only on $\mathfrak p$; dividing by $c = \prod_{\mathfrak p} c_{\mathfrak p}^{-m_{\mathfrak p}} \in F^\times$
($c_{\mathfrak p}$ the $S$-uniformizers, unramified so $w(c) = \mathfrak p(c)$) makes $y = y_0/c$ an $S_L$-unit, and
$y/\sigma y = y_0/\sigma y_0$. -/
@[kb "milne2020cft" "Ch. VII §3 (Hilbert 90 for S-units) [unverified]"]
theorem herbrandM1_eq_one (hσ : σ ≠ 1) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ p : HeightOneSpectrum (𝓞 F), p ∉ S → ∃ c : 𝓞 F, c ∈ p.asIdeal ∧ c ∉ p.asIdeal ^ 2 ∧
        ∀ q : HeightOneSpectrum (𝓞 F), q ∉ S → q ≠ p → c ∉ q.asIdeal)
    (hram : ∀ w : HeightOneSpectrum (𝓞 L), under (F := F) w ∉ S →
        w.asIdeal.ramificationIdx (𝓞 F) = 1) :
    herbrandM1 (σS σ S) = 1 := by
  classical
  unfold herbrandM1
  rw [AddSubgroup.relIndex_eq_one]
  intro x hx
  rw [mem_anti] at hx
  set X : Lˣ := ((Additive.toMul x : SUnit _) : Lˣ) with hXdef
  have hσX : Units.map (σ : L →* L) X = X⁻¹ := by
    have := congrArg (fun z => ((Additive.toMul z : SUnit _) : Lˣ)) hx
    simpa [toMul_σS_val] using this
  have hXσ : (X : L) * σ X = 1 := by
    have := congrArg (fun u : Lˣ => (u : L)) hσX
    simp only [Units.coe_map, MonoidHom.coe_ofClass] at this
    rw [this]; simp
  obtain ⟨y₀, hy₀⟩ := hilbert90 σ hσ X hXσ
  have hXval : ∀ w ∉ overS (L := L) S, w.valuationOfNeZero X = 1 :=
    (mem_sUnit_iff _ _).mp (Additive.toMul x).2
  -- σ y₀ = y₀ * X⁻¹
  have hσy₀ : Units.map (σ : L →* L) y₀ = y₀ * X⁻¹ := by
    apply Units.ext
    simp only [Units.coe_map, MonoidHom.coe_ofClass, Units.val_mul]
    have hne : σ (y₀ : L) ≠ 0 := by simp
    rw [Units.val_inv_eq_inv_val, hy₀]; field_simp
  have hinv : ∀ w, w ∉ overS (L := L) S →
      (comapEquiv (σO σ) w).valuationOfNeZero y₀ = w.valuationOfNeZero y₀ := by
    intro w hw
    rw [← valuationOfNeZero_galois, hσy₀, map_mul, map_inv, hXval w hw, inv_one, mul_one]
  choose! c hc1 hc2 hc3 using hS
  choose wp hwp using exists_over (L := L) (F := F)
  have hc0 : ∀ p, p ∉ S → algebraMap (𝓞 F) F (c p) ≠ 0 := by
    intro p hp h
    rw [map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)] at h
    exact hc2 p hp (h ▸ zero_mem _)
  let cu : HeightOneSpectrum (𝓞 F) → Fˣ := fun p =>
    if hp : p ∉ S then Units.mk0 _ (hc0 p hp) else 1
  have hcu_self : ∀ p, p ∉ S → p.valuationOfNeZero (cu p) = Multiplicative.ofAdd (-1 : ℤ) := by
    intro p hp
    rw [← WithZero.coe_inj, HeightOneSpectrum.valuationOfNeZero_eq]
    simp only [cu, dite_eq_left hp, Units.val_mk0]
    rw [valuation_of_mem_not_sq p (hc1 p hp) (hc2 p hp)]
    rfl
  have hcu_other : ∀ p q, p ∉ S → q ∉ S → q ≠ p → q.valuationOfNeZero (cu p) = 1 := by
    intro p q hp hq hqp
    rw [← WithZero.coe_inj, HeightOneSpectrum.valuationOfNeZero_eq]
    simp only [cu, dite_eq_left hp, Units.val_mk0]
    rw [(HeightOneSpectrum.valuation_eq_one_iff_notMem q).mpr (hc3 p hp q hq hqp)]
    rfl
  set T : Finset (HeightOneSpectrum (𝓞 F)) :=
    ((finite_support y₀).toFinset.image (under (F := F))).filter (· ∉ S) with hT
  let m : HeightOneSpectrum (𝓞 F) → ℤ := fun p => Multiplicative.toAdd ((wp p).valuationOfNeZero y₀)
  set C : Fˣ := ∏ p ∈ T, (cu p) ^ (-(m p)) with hC
  have hCval : ∀ q, q ∉ S → q.valuationOfNeZero C =
      if q ∈ T then (wp q).valuationOfNeZero y₀ else 1 := by
    intro q hq
    rw [hC, map_prod]
    split_ifs with hqT
    · rw [← Finset.prod_erase_mul _ _ hqT, map_zpow, hcu_self q hq]
      rw [Finset.prod_eq_one]
      · simp only [m, one_mul, ofAdd_neg, inv_zpow', neg_neg]
        rw [← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_toAdd]
      · intro p hp
        have hpS : p ∉ S := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hp)).2
        rw [map_zpow, hcu_other p q hpS hq (Finset.ne_of_mem_erase hp).symm, one_zpow]
    · refine Finset.prod_eq_one fun p hp => ?_
      have hpS : p ∉ S := (Finset.mem_filter.mp hp).2
      have hqp : q ≠ p := fun h => hqT (h ▸ hp)
      rw [map_zpow, hcu_other p q hpS hq hqp, one_zpow]
  set CL : Lˣ := Units.map (algebraMap F L : F →* L) C with hCL
  set y : Lˣ := y₀ * CL⁻¹ with hy
  have hyS : y ∈ SUnit (F := L) (overS (L := L) S) := by
    rw [mem_sUnit_iff]
    intro w hw
    have hpS : under (F := F) w ∉ S := by simpa [mem_overS] using hw
    rw [hy, map_mul, map_inv, hCL, valuationOfNeZero_algebraMap, hram w hpS, pow_one,
      hCval _ hpS]
    split_ifs with hT'
    · have hw' : wp (under (F := F) w) ∉ overS (L := L) S := by
        simpa [mem_overS, hwp] using hpS
      have key : w.valuationOfNeZero y₀ = (wp (under (F := F) w)).valuationOfNeZero y₀ := by
        rcases over_eq_or σ hσ (wp (under w)) w (hwp (under w)) with h | h
        · exact congrArg (fun v : HeightOneSpectrum (𝓞 L) => v.valuationOfNeZero y₀) h
        · have := hinv _ hw'
          rw [← this]
          exact congrArg (fun v : HeightOneSpectrum (𝓞 L) => v.valuationOfNeZero y₀) h
      rw [key, mul_inv_cancel]
    · rw [inv_one, mul_one]
      by_contra hne
      apply hT'
      rw [hT, Finset.mem_filter, Finset.mem_image]
      exact ⟨⟨w, by simpa using hne, rfl⟩, hpS⟩
  refine ⟨Additive.ofMul ⟨y, hyS⟩, ?_⟩
  apply Additive.toMul.injective; apply Subtype.ext; apply Units.ext
  rw [diffHom_apply, toMul_sub]
  simp only [toMul_ofMul, Subgroup.coe_div, Units.val_div_eq_div_val, toMul_σS_val, Units.coe_map,
    MonoidHom.coe_ofClass]
  change ((y : L) / σ (y : L)) = (X : L)
  have hσC : σ (CL : L) = (CL : L) := by
    simp only [hCL, Units.coe_map, MonoidHom.coe_ofClass]
    exact σ.commutes _
  rw [hy, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hσC, hy₀]
  have h1 : (CL : L) ≠ 0 := CL.ne_zero
  have h2 : σ (y₀ : L) ≠ 0 := by simp
  field_simp


omit [Algebra.IsQuadraticExtension F L] in
lemma relIndex_range_eq_index_comap' {M N : Type*} [AddCommGroup M] [AddCommGroup N] (f : M →+ N)
    (H : AddSubgroup N) : H.relIndex f.range = (H.comap f).index := by
  rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ f.rangeRestrict_surjective]
  congr 1

/-- The subgroup of `F_S` of norms of `S_L`-units. -/
def normsF (S : Finset (HeightOneSpectrum (𝓞 F))) : AddSubgroup (Additive (SUnit (F := F) S)) :=
  (normHom (σS σ S)).range.comap (inclS (L := L) S)

/-- The index $[F_S^\times : N L_{S_L}^\times]$ is the Tate index $h^0$ of the $S_L$-units. -/
lemma index_normsF (hσ : σ ≠ 1) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    (normsF σ S).index = herbrand0 (σS σ S) := by
  unfold herbrand0 normsF
  rw [← range_inclS σ hσ S, relIndex_range_eq_index_comap']

/-- **The global norm index of `S`-units** (the "first inequality" count): if $\sigma \ne 1$, $h^{-1} = 1$ (e.g.
`herbrandM1_eq_one`), then
$$[F_S^\times : N L_{S_L}^\times] \cdot 2^{\operatorname{rk} L_{S_L}^\times} = 2^{2\operatorname{rk} F_S^\times},$$
with $\operatorname{rk} F_S^\times = r_\infty(F) - 1 + |S|$ and $\operatorname{rk} L_{S_L}^\times = r_\infty(L) - 1 + |S_L|$.
(*Proof.* `herbrand_formula` and `finrank_fixed_add_anti` for $\sigma$ on $L_{S_L}^\times$, whose fixed part is
$F_S^\times$ by `range_inclS`.) -/
@[kb "milne2020cft" "Ch. VII §3 (Herbrand quotient of S-units) [unverified]"]
theorem index_normsF_mul (hσ : σ ≠ 1) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (h1 : herbrandM1 (σS σ S) = 1) :
    (normsF σ S).index * 2 ^ (Units.rank L + (overS (L := L) S).card) =
      2 ^ (2 * (Units.rank F + S.card)) := by
  have hinvol : ∀ x, σS σ S (σS σ S x) = x := by
    intro x
    apply Additive.toMul.injective; apply Subtype.ext; apply Units.ext
    simp [apply_apply]
  obtain ⟨hform, h0, hm⟩ := herbrand_formula hinvol
  have hrk := finrank_fixed_add_anti hinvol
  rw [finrank_sUnit] at hrk
  have hP : finrank ℤ (diffHom (σS σ S)).ker = Units.rank F + S.card := by
    rw [← range_inclS σ hσ S, ← finrank_sUnit (F := F) S]
    exact (AddMonoidHom.ofInjective (inclS_injective (L := L) S)).toIntLinearEquiv.finrank_eq.symm
  rw [index_normsF σ hσ, h1, one_mul] at *
  rw [hP] at hform hrk
  rw [hrk, pow_add, mul_comm (2 ^ (Units.rank F + S.card)), ← mul_assoc, hform, ← pow_add, two_mul]

end Quadratic

end QuadFormsKB.HN

end
