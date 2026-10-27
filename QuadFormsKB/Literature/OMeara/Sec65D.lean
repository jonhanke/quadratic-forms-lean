/-
# O'Meara §65C: spots with prescribed squares among the $S$-units (65:17, 65:18, 65:18a, 65:20)

**Setting** (as in `Sec65C.lean`): $F$ is a number field, $T$ a finite set of finite spots, and O'Meara's $S$ is the set
of finite spots outside $T$ (so $\Omega - S$ is $T$ together with the infinite spots, $s = \lvert T\rvert + r_\infty$);
$\mathfrak u$ = `HN.SUnit T`, and generators of $\mathfrak u$ modulo $\mathfrak u^2$ are `IsGenModSq T e`.
"$\varepsilon$ is a square at $\mathfrak p$" means a square in $F_\mathfrak p$.

**Proves**
* Proposition 65:17 (p. 183): for a set of $s$ generators $\varepsilon_1, \dots, \varepsilon_s$ and an index $i$, there
  are infinitely many $\mathfrak p \in S$ at which $\varepsilon_i$ is a non-square and every other $\varepsilon_j$ is a
  square (`infinite_nonsquare_one`). O'Meara takes $i = 1$; the other indices follow by renumbering. Only the
  finiteness of $T$ is used (not O'Meara's conventions (i), (iii), (iv));
* Proposition 65:18 (p. 184): there are distinct $\mathfrak p_1, \dots, \mathfrak p_s \in S$ with $\varepsilon_i$ a
  non-square at $\mathfrak p_i$ and a square at the other $\mathfrak p_j$ (`exists_dual_spots`);
* Corollary 65:18a (p. 184): under (i)–(iv), an element that is a square at every spot of $\Omega - S$ and a unit at
  every spot of $S - \{\mathfrak p_1, \dots, \mathfrak p_s\}$ is a square (`isSquare_of_dual_spots`);
* Proposition 65:20 (pp. 184–185): for an $S$-unit $\varepsilon$ there are distinct $\mathfrak q, \mathfrak q' \in S$ at
  which $\varepsilon$ is a square and which have the same square $S$-units (`exists_twin_spots`).
-/
import QuadFormsKB.Literature.OMeara.Sec65C
import QuadFormsKB.Literature.OMeara.Sec65A
import QuadFormsKB.Literature.OMeara.Sec65B
import QuadFormsKB.Literature.HasseNorm.GoodPrimes
import QuadFormsKB.Literature.HasseNorm.KummerSquares

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

namespace QuadFormsKB.OMeara

/-! ### Auxiliary: non-squares modulo a prime, and the tower step (internal) -/

namespace Sec65DAux

section General

variable {K : Type} [Field K] [NumberField K]

/-- `a` is not a square modulo `v`. -/
def NSqMod (v : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) : Prop := ∀ r : 𝓞 K, a - r ^ 2 ∉ v.asIdeal

lemma exists_nsq_prime (a : 𝓞 K) (ha : ¬ IsSquare (a : K)) (B : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ v : HeightOneSpectrum (𝓞 K), v ∉ B ∧ (2 * a) ∉ v.asIdeal ∧ NSqMod v a := by
  classical
  obtain ⟨L, _, _, _, s, hs, hspan⟩ := QuadFormsKB.Lam.exists_quadExt (a : K) ha
  obtain ⟨hQ, -⟩ := HN.quadData (a : K) ha s hs hspan
  have hdeg : Module.finrank K L = 2 := Algebra.IsQuadraticExtension.finrank_eq_two K L
  have ha0 : a ≠ 0 := by rintro rfl; exact ha ⟨0, by simp⟩
  have hbad : {p : HeightOneSpectrum (𝓞 K) | 2 * a ∈ p.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {2 * a})
      (by simpa using mul_ne_zero two_ne_zero ha0)).subset ?_
    intro p hp
    rw [Set.mem_ofPred_eq, Ideal.dvd_span_singleton]; exact hp
  by_contra hgoal
  push Not at hgoal
  apply SqLG.not_almost_all_split (F := K) (L := L) (a : K) ha s hs hspan (B ∪ hbad.toFinset)
  intro v hv
  have hvB : v ∉ B := fun h => hv (Finset.mem_union_left _ h)
  have hv2 : 2 * a ∉ v.asIdeal := fun h => hv (Finset.mem_union_right _ (by simpa using h))
  have h3 := hgoal v hvB hv2
  simp only [NSqMod, not_forall, not_not] at h3
  obtain ⟨r, hr⟩ := h3
  obtain ⟨P, Q, hPQ, hP, hQ⟩ := SqLG.exists_two_primes_over a ha s hs hspan v hv2 r hr
  obtain ⟨n1, n2⟩ := SqLG.absNorm_eq_of_two_primes hdeg v P Q hPQ hP hQ
  exact ⟨P, Q, hPQ, hP, hQ, n1, n2⟩

lemma not_nsqMod_of_mul (v : HeightOneSpectrum (𝓞 K)) {x y : 𝓞 K} (hx : NSqMod v x)
    (hxy : NSqMod v (x * y)) : ¬ NSqMod v y := by
  classical
  intro hy
  haveI := v.isMaximal
  letI := Ideal.Quotient.field v.asIdeal
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  letI := Fintype.ofFinite (𝓞 K ⧸ v.asIdeal)
  have key : ∀ z : 𝓞 K, NSqMod v z → ¬ IsSquare (Ideal.Quotient.mk v.asIdeal z) := by
    rintro z hz ⟨w, hw⟩
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective w
    exact hz r (by rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, hw, pow_two, sub_self])
  have h1 := quadraticChar_neg_one_iff_not_isSquare.mpr (key x hx)
  have h2 := quadraticChar_neg_one_iff_not_isSquare.mpr (key y hy)
  have h3 : quadraticChar (𝓞 K ⧸ v.asIdeal) (Ideal.Quotient.mk v.asIdeal (x * y)) = 1 := by
    rw [map_mul (Ideal.Quotient.mk _), map_mul (quadraticChar _), h1, h2]; norm_num
  have h4 : Ideal.Quotient.mk v.asIdeal (x * y) ≠ 0 := fun h => key _ hxy (h ▸ ⟨0, by simp⟩)
  exact key _ hxy ((quadraticChar_one_iff_isSquare h4).mp h3)

end General

section Tower

variable {F H : Type} [Field F] [NumberField F] [Field H] [NumberField H] [Algebra F H]

/-- The prime of `F` below a prime of `H`. -/
def underG (w : HeightOneSpectrum (𝓞 H)) : HeightOneSpectrum (𝓞 F) where
  asIdeal := w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 H))
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := Ideal.IsIntegral.under_ne_bot (𝓞 F) w.ne_bot

/-- The primes of `H` above a finite set of primes of `F`. -/
def overSG (S : Finset (HeightOneSpectrum (𝓞 F))) : Finset (HeightOneSpectrum (𝓞 H)) :=
  Set.Finite.toFinset (s := {w : HeightOneSpectrum (𝓞 H) | underG (F := F) w ∈ S}) (by
    classical
    have : {w : HeightOneSpectrum (𝓞 H) | underG (F := F) w ∈ S} ⊆
        ⋃ p ∈ S, {w : HeightOneSpectrum (𝓞 H) |
          w.asIdeal ∣ p.asIdeal.map (algebraMap (𝓞 F) (𝓞 H))} := by
      intro w hw
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
      refine ⟨underG w, hw, ?_⟩
      rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap]
      exact le_rfl
    refine Set.Finite.subset (Set.Finite.biUnion S.finite_toSet fun p _ => ?_) this
    apply Ideal.finite_factors
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective
      (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 H))]
    exact p.ne_bot)

lemma mem_overSG {S : Finset (HeightOneSpectrum (𝓞 F))} {w : HeightOneSpectrum (𝓞 H)} :
    w ∈ overSG S ↔ underG (F := F) w ∈ S := by
  simp [overSG]

lemma core (a : 𝓞 F) (hna : ¬ IsSquare (algebraMap F H (a : F))) {ι : Type} [Fintype ι]
    (a' : ι → 𝓞 F) (ha'0 : ∀ j, a' j ≠ 0) (hsq : ∀ j, IsSquare (algebraMap F H (a' j : F)))
    (B : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ p : HeightOneSpectrum (𝓞 F), p ∉ B ∧ (2 : 𝓞 F) ∉ p.asIdeal ∧ (∀ j, a' j ∉ p.asIdeal) ∧
      NSqMod p a ∧ ∀ j, ¬ NSqMod p (a' j) := by
  classical
  have ha0 : a ≠ 0 := by rintro rfl; exact hna ⟨0, by simp⟩
  set m : 𝓞 F := 2 * a * ∏ j, a' j with hm
  have hm0 : m ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero ha0) (Finset.prod_ne_zero_iff.mpr fun j _ => ha'0 j)
  have hbad : {p : HeightOneSpectrum (𝓞 F) | m ∈ p.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {m}) (by simpa using hm0)).subset ?_
    intro p hp
    rw [Set.mem_ofPred_eq, Ideal.dvd_span_singleton]; exact hp
  set B' := B ∪ hbad.toFinset with hB'
  set aH : 𝓞 H := algebraMap (𝓞 F) (𝓞 H) a with haHdef
  have haH : ¬ IsSquare (aH : H) := hna
  obtain ⟨P, hPB, hP2, hPn⟩ := exists_nsq_prime aH haH (overSG (F := F) B')
  set p := underG (F := F) P with hpdef
  have hcomap : ∀ c : 𝓞 F, algebraMap (𝓞 F) (𝓞 H) c ∈ P.asIdeal ↔ c ∈ p.asIdeal :=
    fun c => Iff.rfl
  have hpB' : p ∉ B' := fun h => hPB (mem_overSG.2 h)
  have hpB : p ∉ B := fun h => hpB' (Finset.mem_union_left _ h)
  have hpm : m ∉ p.asIdeal := fun h => hpB' (Finset.mem_union_right _ (by simpa using h))
  have hp2 : (2 : 𝓞 F) ∉ p.asIdeal := fun h =>
    hpm (p.asIdeal.mul_mem_right _ (p.asIdeal.mul_mem_right _ h))
  have hpa : a ∉ p.asIdeal := fun h =>
    hpm (p.asIdeal.mul_mem_right _ (p.asIdeal.mul_mem_left _ h))
  have hpj : ∀ j, a' j ∉ p.asIdeal := by
    intro j h
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem a' (Finset.mem_univ j)
    apply hpm
    rw [hm, hc]
    exact p.asIdeal.mul_mem_left _ (p.asIdeal.mul_mem_right _ h)
  have hpn : NSqMod p a := by
    intro r hr
    apply hPn (algebraMap (𝓞 F) (𝓞 H) r)
    have := (hcomap (a - r ^ 2)).2 hr
    rwa [map_sub, map_pow] at this
  refine ⟨p, hpB, hp2, hpj, hpn, fun j => ?_⟩
  refine not_nsqMod_of_mul p hpn ?_
  intro r hr
  obtain ⟨h, hh⟩ := hsq j
  have hint : IsIntegral ℤ h := IsIntegral.of_pow two_pos (by
    rw [pow_two, ← hh]; exact (RingOfIntegers.isIntegral_coe (a' j)).algebraMap)
  set ρ : 𝓞 H := ⟨h, hint⟩ with hρdef
  have hρ : ρ ^ 2 = algebraMap (𝓞 F) (𝓞 H) (a' j) := by
    apply RingOfIntegers.ext
    show h ^ 2 = algebraMap F H (a' j : F)
    rw [pow_two, ← hh]
  have hρP : ρ ∉ P.asIdeal := by
    intro hρP
    apply hpj j
    rw [← hcomap, ← hρ]
    exact P.asIdeal.pow_mem_of_mem hρP 2 (by norm_num)
  obtain ⟨y, i, hi, hyi⟩ := Ideal.IsMaximal.exists_inv P.isMaximal hρP
  have hR : aH * ρ ^ 2 - (algebraMap (𝓞 F) (𝓞 H) r) ^ 2 ∈ P.asIdeal := by
    have := (hcomap (a * a' j - r ^ 2)).2 hr
    rwa [map_sub, map_pow, map_mul, ← hρ] at this
  apply hPn (algebraMap (𝓞 F) (𝓞 H) r * y)
  have hi' : i = 1 - y * ρ := by linear_combination hyi
  have e : aH - (algebraMap (𝓞 F) (𝓞 H) r * y) ^ 2 =
      aH * i * (1 + ρ * y) + y ^ 2 * (aH * ρ ^ 2 - (algebraMap (𝓞 F) (𝓞 H) r) ^ 2) := by
    rw [hi']; ring
  rw [e]
  exact P.asIdeal.add_mem (P.asIdeal.mul_mem_right _ (P.asIdeal.mul_mem_left _ hi))
    (P.asIdeal.mul_mem_left _ hR)

end Tower

end Sec65DAux

variable {F : Type} [Field F] [NumberField F]

local notation "sq" T => Fin (Finset.card T + Fintype.card (InfinitePlace F))

/-- "$\varepsilon$ is a square at the finite spot $\mathfrak p$". -/
abbrev SqAt (v : HeightOneSpectrum (𝓞 F)) (x : F) : Prop := IsSquare (algebraMap F (v.adicCompletion F) x)

namespace Sec65DAux

section Local

lemma isSquare_alg_iff {R S : Type*} [Field R] [Field S] [Algebra R S] {x d a : R} (hd : d ≠ 0)
    (h : a = x * d ^ 2) : IsSquare (algebraMap R S a) ↔ IsSquare (algebraMap R S x) := by
  have hd' : algebraMap R S d ≠ 0 := fun h0 => hd ((algebraMap R S).injective (by rw [h0, map_zero]))
  rw [h, map_mul, map_pow]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y / algebraMap R S d, by field_simp; linear_combination hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y * algebraMap R S d, by rw [hy]; ring⟩

lemma exists_int_scale (x : F) (hx : x ≠ 0) :
    ∃ (a : 𝓞 F) (d : F), a ≠ 0 ∧ d ≠ 0 ∧ (a : F) = x * d ^ 2 := by
  obtain ⟨n, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
  have hy0 : (y : F) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  have hxy' : (n : F) / (y : F) = x := hxy
  have heq : (((n * y : 𝓞 F)) : F) = x * (y : F) ^ 2 := by
    rw [← hxy']; push_cast; field_simp
  have hne : (((n * y : 𝓞 F)) : F) ≠ 0 := by
    rw [heq]; exact mul_ne_zero hx (pow_ne_zero 2 hy0)
  exact ⟨n * y, (y : F), fun h => hne (by rw [h]; rfl), hy0, heq⟩

lemma sqAt_scale (v : HeightOneSpectrum (𝓞 F)) {x d a : F} (hd : d ≠ 0) (h : a = x * d ^ 2) :
    SqAt v a ↔ SqAt v x := isSquare_alg_iff hd h

lemma sqAt_of_sq_mod (v : HeightOneSpectrum (𝓞 F)) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) {a : 𝓞 F}
    (hav : a ∉ v.asIdeal) {r : 𝓞 F} (hr : a - r ^ 2 ∈ v.asIdeal) : SqAt v (a : F) := by
  have hct : r ∉ v.asIdeal := by
    intro hc'
    apply hav
    have : a = (a - r ^ 2) + r * r := by ring
    rw [this]; exact v.asIdeal.add_mem hr (v.asIdeal.mul_mem_left _ hc')
  have hcF : (r : F) ≠ 0 := by
    intro h0; apply hct
    rw [show r = 0 from (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mp h0]
    exact zero_mem _
  have hval : v.valuation F ((a : F) / (r : F) ^ 2 - 1) < 1 := by
    have e : (a : F) / (r : F) ^ 2 - 1 = algebraMap (𝓞 F) F (a - r ^ 2) / (r : F) ^ 2 := by
      rw [map_sub, map_pow]; field_simp
    have hvc : v.valuation F (r : F) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem v).mpr hct
    rw [e, map_div₀, map_pow, hvc, one_pow, div_one]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem v _).mpr hr
  obtain ⟨u, hu⟩ := NFLocal.isSquare_of_valuation_sub_one_lt_nf v h2 _ hval
  refine ⟨u * algebraMap F _ (r : F), ?_⟩
  have : (a : F) = (a : F) / (r : F) ^ 2 * ((r : F) * (r : F)) := by field_simp
  rw [this, map_mul, hu, map_mul]; ring

/-- Products of distinct generators are non-squares in `F`. -/
lemma prod_not_isSquare (T : Finset (HeightOneSpectrum (𝓞 F))) {e : (sq T) → HN.SUnit (F := F) T}
    (he : IsGenModSq T e) (s : Finset (sq T)) (hs : s.Nonempty) :
    ¬ IsSquare (∏ i ∈ s, ((e i : Fˣ) : F)) := by
  classical
  haveI := (sunit_vq T).1
  intro hsq
  obtain ⟨c, hc⟩ := hsq
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hc
    exact (Finset.prod_ne_zero_iff.mpr fun i _ => (e i : Fˣ).ne_zero) hc
  have hcT : ∀ v ∉ (↑T : Set (HeightOneSpectrum (𝓞 F))), v.valuation F c = 1 := by
    intro v hv
    have h1 : v.valuation F c * v.valuation F c = 1 := by
      rw [← map_mul, ← hc, map_prod]
      exact Finset.prod_eq_one fun i _ => (e i).2 v hv
    have : v.valuation F c ^ 2 = 1 ^ 2 := by rw [pow_two, h1]; simp
    exact (pow_left_inj₀ zero_le' zero_le' two_ne_zero).mp this
  let d : HN.SUnit (F := F) T := ⟨Units.mk0 c hc0, fun v hv => hcT v hv⟩
  let ι : HN.SUnit (F := F) T →* F := (Units.coeHom F).comp (HN.SUnit (F := F) T).subtype
  have hι : Function.Injective ι := fun x y h => Subtype.ext (Units.ext h)
  let ν : (sq T) → ℕ := fun i => if i ∈ s then 1 else 0
  have hν : ∀ i, ν i ≤ 1 := fun i => by simp only [ν]; split_ifs <;> omega
  have heq : (∏ i, e i ^ ν i) * (1 : HN.SUnit (F := F) T) ^ 2 =
      (∏ i, e i ^ (fun _ => (0 : ℕ)) i) * d ^ 2 := by
    apply hι
    simp only [map_mul, map_prod, map_pow, map_one, pow_zero, Finset.prod_const_one, one_pow, mul_one,
      one_mul]
    have h3 : ∏ i, ι (e i) ^ ν i = ∏ i ∈ s, ι (e i) := by
      simp [ν, pow_ite]
    rw [h3]
    have h4 : ι d = c := rfl
    rw [h4, pow_two, ← hc]
    rfl
  have hu := Mod2.genP_unique (sunit_vq T).2 he hν (fun _ => by simp) heq
  obtain ⟨i, hi⟩ := hs
  have := congrFun hu i
  simp [ν, hi] at this

/-- Evaluation of an $S$-unit in the completion at `v`. -/
def psi (v : HeightOneSpectrum (𝓞 F)) (T : Finset (HeightOneSpectrum (𝓞 F))) :
    HN.SUnit (F := F) T →* v.adicCompletion F :=
  (algebraMap F (v.adicCompletion F) : F →* v.adicCompletion F).comp
    ((Units.coeHom F).comp (HN.SUnit (F := F) T).subtype)

lemma psi_apply (v : HeightOneSpectrum (𝓞 F)) (T : Finset (HeightOneSpectrum (𝓞 F)))
    (δ : HN.SUnit (F := F) T) : psi v T δ = algebraMap F (v.adicCompletion F) ((δ : Fˣ) : F) := rfl

lemma psi_ne (v : HeightOneSpectrum (𝓞 F)) (T : Finset (HeightOneSpectrum (𝓞 F)))
    (δ : HN.SUnit (F := F) T) : psi v T δ ≠ 0 := fun h =>
  (δ : Fˣ).ne_zero ((algebraMap F (v.adicCompletion F)).injective (by rw [← psi_apply, h, map_zero]))

lemma isSquare_mul_sq_iff {K : Type*} [Field K] {y c : K} (hc : c ≠ 0) :
    IsSquare (y * c ^ 2) ↔ IsSquare y := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w / c, by field_simp; linear_combination hw⟩
  · rintro ⟨w, hw⟩
    exact ⟨w * c, by rw [hw]; ring⟩

lemma isSquare_pow_iff {K : Type*} [Field K] {x : K} (hx : x ≠ 0) (hns : ¬ IsSquare x) (ν : ℕ) :
    IsSquare (x ^ ν) ↔ Even ν := by
  constructor
  · intro h
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    obtain ⟨k, rfl⟩ := hodd
    apply hns
    have : x ^ (2 * k + 1) = x * (x ^ k) ^ 2 := by ring
    rw [this] at h
    exact (isSquare_mul_sq_iff (pow_ne_zero k hx)).1 h
  · rintro ⟨k, rfl⟩
    exact ⟨x ^ k, by ring⟩

lemma isSquare_psi_prod_iff (v : HeightOneSpectrum (𝓞 F)) (T : Finset (HeightOneSpectrum (𝓞 F))) {r : ℕ}
    (e : Fin r → HN.SUnit (F := F) T) (m : Fin r) (hm : ¬ IsSquare (psi v T (e m)))
    (hj : ∀ j, j ≠ m → IsSquare (psi v T (e j))) (ν : Fin r → ℕ) (d : HN.SUnit (F := F) T) :
    IsSquare (psi v T ((∏ i, e i ^ ν i) * d ^ 2)) ↔ Even (ν m) := by
  classical
  simp only [map_mul, map_prod, map_pow]
  rw [← Finset.mul_prod_erase Finset.univ (fun i => psi v T (e i) ^ ν i) (Finset.mem_univ m),
    mul_assoc]
  have hRsq : IsSquare ((∏ i ∈ Finset.univ.erase m, psi v T (e i) ^ ν i) * psi v T d ^ 2) := by
    refine IsSquare.mul ?_ ⟨psi v T d, pow_two _⟩
    refine Finset.prod_induction _ IsSquare (fun a b => IsSquare.mul) ⟨1, by simp⟩ ?_
    intro i hi
    exact (hj i (Finset.ne_of_mem_erase hi)).pow _
  have hR0 : (∏ i ∈ Finset.univ.erase m, psi v T (e i) ^ ν i) * psi v T d ^ 2 ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (psi_ne v T _))
      (pow_ne_zero _ (psi_ne v T _))
  obtain ⟨c, hc⟩ := hRsq
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hR0
    rw [hc, mul_zero]
  rw [hc, ← pow_two, isSquare_mul_sq_iff hc0]
  exact isSquare_pow_iff (psi_ne v T _) hm _

lemma isSquare_psi_prod_of_all (v : HeightOneSpectrum (𝓞 F)) (T : Finset (HeightOneSpectrum (𝓞 F)))
    {r : ℕ} (e : Fin r → HN.SUnit (F := F) T) (h : ∀ j, IsSquare (psi v T (e j)))
    (ν : Fin r → ℕ) (d : HN.SUnit (F := F) T) : IsSquare (psi v T ((∏ i, e i ^ ν i) * d ^ 2)) := by
  simp only [map_mul, map_prod, map_pow]
  refine IsSquare.mul ?_ ⟨psi v T d, pow_two _⟩
  refine Finset.prod_induction _ IsSquare (fun a b => IsSquare.mul) ⟨1, by simp⟩ ?_
  intro i _
  exact (h i).pow _

lemma exists_two_of_infinite {α : Type*} {S : Set α} (hS : S.Infinite) :
    ∃ q q', q ≠ q' ∧ q ∈ S ∧ q' ∈ S := by
  obtain ⟨q, hq⟩ := hS.nonempty
  obtain ⟨q', hq'⟩ := (hS.sdiff (Set.finite_singleton q)).nonempty
  exact ⟨q, q', fun h => hq'.2 (by simp [h]), hq, hq'.1⟩

end Local

end Sec65DAux

open Sec65DAux in
/-- Auxiliary form of 65:17 (internal). -/
lemma infinite_aux (T : Finset (HeightOneSpectrum (𝓞 F))) {e : (sq T) → HN.SUnit (F := F) T}
    (he : IsGenModSq T e) (i : sq T) :
    {v : HeightOneSpectrum (𝓞 F) | v ∉ T ∧ ¬ SqAt v ((e i : Fˣ) : F) ∧
      ∀ j, j ≠ i → SqAt v ((e j : Fˣ) : F)}.Infinite := by
  classical
  have hb0 := fun j => IsAlgClosed.exists_pow_nat_eq
    (algebraMap F (AlgebraicClosure F) ((e j : Fˣ) : F)) (n := 2) two_pos
  choose b hb using hb0
  choose A D hA hD hAD using fun j : sq T => exists_int_scale ((e j : Fˣ) : F) (e j : Fˣ).ne_zero
  have hchar : ringChar F ≠ 2 := by rw [ringChar.eq_zero]; norm_num
  have hprod := prod_not_isSquare T he
  have hK : Module.finrank F (IntermediateField.adjoin F (Set.range b)) =
      2 ^ (T.card + Fintype.card (InfinitePlace F)) :=
    finrank_adjoin_sqrt hchar b (fun j => ((e j : Fˣ) : F)) hb hprod
  let ι := {j : sq T // j ≠ i}
  let Hs : IntermediateField F (AlgebraicClosure F) :=
    IntermediateField.adjoin F (Set.range fun j : ι => b j.1)
  let σ : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hH : Module.finrank F Hs = 2 ^ Fintype.card ι := by
    have hrange : Set.range (fun k : Fin (Fintype.card ι) => b (σ k).1) =
        Set.range (fun j : ι => b j.1) := by
      ext x; constructor
      · rintro ⟨k, rfl⟩; exact ⟨σ k, rfl⟩
      · rintro ⟨j, rfl⟩; exact ⟨σ.symm j, by simp⟩
    have := finrank_adjoin_sqrt hchar (fun k : Fin (Fintype.card ι) => b (σ k).1)
      (fun k => ((e (σ k).1 : Fˣ) : F)) (fun k => hb _) (by
        intro s hs hsq
        refine hprod (s.map ⟨fun k => (σ k).1, fun x y h => σ.injective (Subtype.ext h)⟩)
          (by simpa using hs) ?_
        rw [Finset.prod_map]; exact hsq)
    rw [hrange] at this
    exact this
  have hlt : Fintype.card ι < T.card + Fintype.card (InfinitePlace F) := by
    have := Fintype.card_subtype_lt (p := fun j : sq T => j ≠ i) (x := i) (by simp)
    rw [Fintype.card_fin] at this
    convert this
  have hfd : FiniteDimensional F Hs := Module.finite_of_finrank_pos (by rw [hH]; positivity)
  haveI : NumberField Hs := NumberField.of_module_finite F Hs
  have hnsq : ¬ IsSquare (algebraMap F Hs ((e i : Fˣ) : F)) := by
    rintro ⟨h, hh⟩
    have h1 : (h : AlgebraicClosure F) ^ 2 = (b i) ^ 2 := by
      rw [hb i, pow_two]
      have := congrArg (fun z : Hs => (z : AlgebraicClosure F)) hh
      simpa using this.symm
    have hbi : b i ∈ Hs := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h2 | h2
      · rw [← h2]; exact h.2
      · have : b i = -(h : AlgebraicClosure F) := by rw [h2, neg_neg]
        rw [this]; exact neg_mem h.2
    have hle : IntermediateField.adjoin F (Set.range b) ≤ Hs := by
      apply IntermediateField.adjoin_le_iff.mpr
      rintro _ ⟨j, rfl⟩
      by_cases hj : j = i
      · rw [hj]; exact hbi
      · exact IntermediateField.subset_adjoin F _ ⟨⟨j, hj⟩, rfl⟩
    have hge : Hs ≤ IntermediateField.adjoin F (Set.range b) := by
      apply IntermediateField.adjoin_le_iff.mpr
      rintro _ ⟨j, rfl⟩
      exact IntermediateField.subset_adjoin F _ ⟨j.1, rfl⟩
    have heq := le_antisymm hle hge
    rw [heq, hH] at hK
    exact absurd (Nat.pow_right_injective le_rfl hK) (ne_of_lt hlt)
  have hnsqA : ¬ IsSquare (algebraMap F Hs ((A i : 𝓞 F) : F)) := by
    rw [isSquare_alg_iff (hD i) (hAD i)]; exact hnsq
  have hsqH : ∀ j : ι, IsSquare (algebraMap F Hs ((A j.1 : 𝓞 F) : F)) := by
    intro j
    rw [isSquare_alg_iff (hD j.1) (hAD j.1)]
    refine ⟨⟨b j.1, IntermediateField.subset_adjoin F _ ⟨j, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    show algebraMap F (AlgebraicClosure F) _ = b j.1 * b j.1
    rw [← pow_two, hb]
  have hmain : ∀ Bf : Finset (HeightOneSpectrum (𝓞 F)), ∃ v ∈ {v : HeightOneSpectrum (𝓞 F) |
      v ∉ T ∧ ¬ SqAt v ((e i : Fˣ) : F) ∧ ∀ j, j ≠ i → SqAt v ((e j : Fˣ) : F)}, v ∉ Bf := by
    intro Bf
    obtain ⟨p, hpB, hp2, hpj, hpn, hpj'⟩ :=
      core (H := Hs) (A i) hnsqA (fun j : ι => A j.1) (fun j => hA j.1) hsqH (T ∪ Bf)
    have hpT : p ∉ T := fun h => hpB (Finset.mem_union_left _ h)
    have hpBf : p ∉ Bf := fun h => hpB (Finset.mem_union_right _ h)
    refine ⟨p, ⟨hpT, ?_, ?_⟩, hpBf⟩
    · intro hsqp
      have hA' : SqAt p ((A i : 𝓞 F) : F) := (sqAt_scale p (hD i) (hAD i)).2 hsqp
      have hAi : A i ∉ p.asIdeal := fun h => hpn 0 (by simpa using h)
      have h2A : 2 * A i ∉ p.asIdeal := by
        intro h
        rcases p.isPrime.mem_or_mem h with h' | h'
        · exact hp2 h'
        · exact hAi h'
      obtain ⟨r, hr⟩ := SqLG.exists_sq_mod_of_isSquare (A i) p h2A hA'
      exact hpn r hr
    · intro j hj
      have h1 := hpj' ⟨j, hj⟩
      simp only [NSqMod, not_forall, not_not] at h1
      obtain ⟨r, hr⟩ := h1
      exact (sqAt_scale p (hD j) (hAD j)).1 (sqAt_of_sq_mod p hp2 (hpj ⟨j, hj⟩) hr)
  by_contra hfin
  rw [Set.not_infinite] at hfin
  obtain ⟨v, hv, hvn⟩ := hmain hfin.toFinset
  exact hvn (hfin.mem_toFinset.2 hv)

/-- **Proposition 65:17** (O'Meara 1963, p. 183): let $\varepsilon_1, \dots, \varepsilon_s$ be a set of generators of
$\mathfrak u$ modulo $\mathfrak u^2$ and $i$ an index. There are infinitely many spots $\mathfrak p \in S$ such that
$\varepsilon_i$ is a non-square at $\mathfrak p$ and $\varepsilon_j$ is a square at $\mathfrak p$ for every $j \ne i$. -/
@[kb "omeara1963" "§65C, 65:17, p. 183 (infinitely many 𝔭 ∈ S with ε₁ a non-square and ε₂, …, ε_s squares)"]
theorem infinite_nonsquare_one (T : Finset (HeightOneSpectrum (𝓞 F))) {e : (sq T) → HN.SUnit (F := F) T}
    (he : IsGenModSq T e) (i : sq T) :
    {v : HeightOneSpectrum (𝓞 F) | v ∉ T ∧ ¬ SqAt v ((e i : Fˣ) : F) ∧
      ∀ j, j ≠ i → SqAt v ((e j : Fˣ) : F)}.Infinite :=
  infinite_aux T he i

/-- **Proposition 65:18** (O'Meara 1963, p. 184): for a set of $s$ generators $\varepsilon_1, \dots, \varepsilon_s$ of
$\mathfrak u$ modulo $\mathfrak u^2$ there are distinct spots $\mathfrak p_1, \dots, \mathfrak p_s \in S$ such that
$\varepsilon_j$ is a square at $\mathfrak p_i$ if and only if $j \ne i$. The spots can be taken non-dyadic. -/
@[kb "omeara1963" "§65C, 65:18, p. 184 (spots 𝔭₁, …, 𝔭_s with ε_i a non-square exactly at 𝔭_i)"]
theorem exists_dual_spots (T : Finset (HeightOneSpectrum (𝓞 F))) {e : (sq T) → HN.SUnit (F := F) T}
    (he : IsGenModSq T e) :
    ∃ p : (sq T) → HeightOneSpectrum (𝓞 F), Function.Injective p ∧ (∀ i, p i ∉ T ∧ (2 : 𝓞 F) ∉ (p i).asIdeal) ∧
      ∀ i j, SqAt (p i) ((e j : Fˣ) : F) ↔ j ≠ i := by
  classical
  have hfin2 : {v : HeightOneSpectrum (𝓞 F) | (2 : 𝓞 F) ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {(2 : 𝓞 F)}) (by simpa using two_ne_zero)).subset ?_
    intro p hp
    rw [Set.mem_ofPred_eq, Ideal.dvd_span_singleton]; exact hp
  have hex : ∀ i, ∃ v : HeightOneSpectrum (𝓞 F), (v ∉ T ∧ ¬ SqAt v ((e i : Fˣ) : F) ∧
      ∀ j, j ≠ i → SqAt v ((e j : Fˣ) : F)) ∧ (2 : 𝓞 F) ∉ v.asIdeal := by
    intro i
    obtain ⟨v, hv, hvn⟩ := (infinite_nonsquare_one T he i).exists_notMem_finset hfin2.toFinset
    exact ⟨v, hv, fun h => hvn (hfin2.mem_toFinset.2 h)⟩
  choose p hp h2 using hex
  refine ⟨p, ?_, fun i => ⟨(hp i).1, h2 i⟩, ?_⟩
  · intro i k hik
    by_contra hne
    have h1 := (hp i).2.2 k (Ne.symm hne)
    rw [hik] at h1
    exact (hp k).2.1 h1
  · intro i j
    by_cases hji : j = i
    · subst hji; simp [(hp j).2.1]
    · simp [hji, (hp i).2.2 j hji]

open scoped Classical in
open Sec65DAux in
/-- For dual spots, the subgroup of $S$-units that are squares at all of them has index $2^s$ (internal). -/
lemma index_kerT_dual (T : Finset (HeightOneSpectrum (𝓞 F))) {e : (sq T) → HN.SUnit (F := F) T}
    (he : IsGenModSq T e) {p : (sq T) → HeightOneSpectrum (𝓞 F)}
    (hp : ∀ i j, SqAt (p i) ((e j : Fˣ) : F) ↔ j ≠ i) :
    (HN.kerT T (Finset.univ.image p)).index = 2 ^ (Finset.univ.image p).card := by
  classical
  haveI := (sunit_vq T).1
  have hrank := (sunit_vq T).2
  have hinj : Function.Injective p := by
    intro i k hik
    by_contra hne
    have h1 := (hp i k).2 (Ne.symm hne)
    rw [hik] at h1
    exact ((hp k k).1 h1) rfl
  have hli : LinearIndependent (ZMod 2) fun i => Mod2.mkq (e i) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank ((Mod2.genP_iff e).mp he) (by simp [hrank])
  let bas := Module.Basis.mk hli ((Mod2.genP_iff e).mp he)
  let Φ : Additive (HN.SUnit (F := F) T) →+ ((sq T) → ZMod 2) :=
    (bas.equivFun : Mod2.Vq (HN.SUnit (F := F) T) →ₗ[ZMod 2] ((sq T) → ZMod 2)).toAddMonoidHom.comp
      (QuotientAddGroup.mk' _)
  have hΦ : ∀ (ν : (sq T) → ℕ) (d : HN.SUnit (F := F) T),
      Φ (Additive.ofMul ((∏ i, e i ^ ν i) * d ^ 2)) = fun i => (ν i : ZMod 2) := by
    intro ν d
    have h1 : (QuotientAddGroup.mk (Additive.ofMul ((∏ i, e i ^ ν i) * d ^ 2)) :
        Mod2.Vq (HN.SUnit (F := F) T)) = ∑ i, (ν i : ZMod 2) • bas i := by
      show Mod2.mkq _ = _
      simp only [Mod2.mkq_mul, Mod2.mkq_sq, Mod2.mkq_prod_pow]
      refine (add_zero (_ : Mod2.Vq (HN.SUnit (F := F) T))).trans ?_
      simp [bas]
    show bas.equivFun (QuotientAddGroup.mk (Additive.ofMul ((∏ i, e i ^ ν i) * d ^ 2))) = _
    rw [h1]
    funext i
    simp [Module.Basis.equivFun_apply, Finsupp.single_apply]
  have hker : HN.kerT T (Finset.univ.image p) = Φ.ker := by
    ext x
    obtain ⟨ν, d, hx⟩ := he (Additive.toMul x)
    have hx' : x = Additive.ofMul ((∏ i, e i ^ ν i) * d ^ 2) := by rw [← hx]; rfl
    subst hx'
    have hiff : ∀ i, SqAt (p i) (HN.toF (Additive.ofMul ((∏ i, e i ^ ν i) * d ^ 2))) ↔
        Even (ν i) := by
      intro i
      exact isSquare_psi_prod_iff (p i) T e i
        (fun h => ((hp i i).1 h) rfl) (fun j hj => (hp i j).2 hj) ν d
    rw [AddMonoidHom.mem_ker, hΦ]
    constructor
    · intro h
      funext i
      have := (hiff i).1 (h (p i) (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
      have h3 := (ZMod.natCast_eq_zero_iff_even).2 this
      exact h3
    · intro h t ht
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ht
      have h3 := congrFun h i
      have : Even (ν i) := (ZMod.natCast_eq_zero_iff_even).1 h3
      exact (hiff i).2 this
  have hsurj : Function.Surjective Φ :=
    (bas.equivFun.surjective).comp (QuotientAddGroup.mk'_surjective _)
  rw [hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hsurj, AddSubgroup.card_top,
    Finset.card_image_of_injective _ hinj]
  simp [Nat.card_eq_fintype_card]

/-- **Corollary 65:18a** (O'Meara 1963, p. 184): assume O'Meara's conventions (i)–(iv) for $S = $ the finite spots
outside $T$, and let $\mathfrak p_1, \dots, \mathfrak p_s$ be as in 65:18 for a set of $s$ generators. If $\alpha \in F$
is a square at every spot of $\Omega - S$ and a unit at every spot of $S - \{\mathfrak p_1, \dots, \mathfrak p_s\}$,
then $\alpha$ is a square. -/
@[kb "omeara1963" "§65C, 65:18a, p. 184 (a square outside S and a unit on S − {𝔭₁, …, 𝔭_s} is a square)"]
theorem isSquare_of_dual_spots (T : Finset (HeightOneSpectrum (𝓞 F))) (hS : SConventions (F := F) (↑T)ᶜ)
    {e : (sq T) → HN.SUnit (F := F) T} (he : IsGenModSq T e) {p : (sq T) → HeightOneSpectrum (𝓞 F)}
    (hpT : ∀ i, p i ∉ T) (hp : ∀ i j, SqAt (p i) ((e j : Fˣ) : F) ↔ j ≠ i) {α : F} (hα : α ≠ 0)
    (hsq : ∀ v ∈ T, SqAt v α) (hinf : ∀ w : InfinitePlace F, IsSquare (algebraMap F w.Completion α))
    (hunit : ∀ v, v ∉ T → v ∉ Set.range p → v.valuation F α = 1) : IsSquare α := by
  classical
  have hidx := index_kerT_dual T he hp
  have hTeq : hS.cofinite.toFinset = T := by ext v; simp
  have hnd : ∀ v, v ∉ T → (2 : 𝓞 F) ∉ v.asIdeal := fun v hv => hS.nondyadic v (by simpa using hv)
  have hU := exists_uniformizer hS
  rw [hTeq] at hU
  have := HN.isSquare_of_isSquare_local (1 : F) T T (Finset.univ.image p) hU (subset_refl _)
    (fun v hv => by by_contra h; exact hnd v h hv)
    (fun t ht => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ht
      exact ⟨hpT i, hnd _ (hpT i), ⟨1, by simp⟩⟩)
    hidx (Units.mk0 α hα) (by
      rw [HN.mem_sUnit_iff]
      intro w hw
      have hwT : w ∉ T := fun h => hw (Finset.mem_union_left _ h)
      have hwp : w ∉ Set.range p := by
        rintro ⟨i, rfl⟩
        exact hw (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
      rw [← WithZero.coe_inj, HeightOneSpectrum.valuationOfNeZero_eq, Units.val_mk0, hunit w hwT hwp]
      rfl)
    (fun v hv => hsq v hv) (fun w => hinf w)
  simpa using this

open Sec65DAux in
/-- Twin spots for a non-square $S$-unit (internal form of 65:20). -/
lemma twin_aux (T : Finset (HeightOneSpectrum (𝓞 F))) {ε' : HN.SUnit (F := F) T}
    (hε' : ¬ IsSquare ((ε' : Fˣ) : F)) :
    ∃ q q' : HeightOneSpectrum (𝓞 F), q ≠ q' ∧ q ∉ T ∧ q' ∉ T ∧ SqAt q ((ε' : Fˣ) : F) ∧
      SqAt q' ((ε' : Fˣ) : F) ∧
      ∀ δ : HN.SUnit (F := F) T, SqAt q ((δ : Fˣ) : F) ↔ SqAt q' ((δ : Fˣ) : F) := by
  classical
  obtain ⟨e, he, k, hk⟩ := exists_isGenModSq_mem T hε'
  by_cases hex : ∃ m : sq T, m ≠ k
  · obtain ⟨m, hm⟩ := hex
    obtain ⟨q, q', hne, hq, hq'⟩ := exists_two_of_infinite (infinite_nonsquare_one T he m)
    refine ⟨q, q', hne, hq.1, hq'.1, ?_, ?_, ?_⟩
    · rw [← hk]; exact hq.2.2 k (Ne.symm hm)
    · rw [← hk]; exact hq'.2.2 k (Ne.symm hm)
    · intro δ
      obtain ⟨ν, d, hδ⟩ := he δ
      have h1 := isSquare_psi_prod_iff q T e m hq.2.1 hq.2.2 ν d
      have h2 := isSquare_psi_prod_iff q' T e m hq'.2.1 hq'.2.2 ν d
      rw [hδ]; exact h1.trans h2.symm
  · push Not at hex
    obtain ⟨q, q', hne, hq, hq'⟩ := exists_two_of_infinite
      ((infinite_isSquare_at ((ε' : Fˣ) : F)).sdiff T.finite_toSet)
    refine ⟨q, q', hne, hq.2, hq'.2, hq.1, hq'.1, ?_⟩
    intro δ
    obtain ⟨ν, d, hδ⟩ := he δ
    have hallq : ∀ j, IsSquare (psi q T (e j)) := fun j => by rw [hex j, hk]; exact hq.1
    have hallq' : ∀ j, IsSquare (psi q' T (e j)) := fun j => by rw [hex j, hk]; exact hq'.1
    rw [hδ]
    exact iff_of_true (isSquare_psi_prod_of_all q T e hallq ν d)
      (isSquare_psi_prod_of_all q' T e hallq' ν d)

/-- **Proposition 65:20** (O'Meara 1963, pp. 184–185): for an $S$-unit $\varepsilon$ there are distinct spots
$\mathfrak q, \mathfrak q' \in S$ such that (i) $\varepsilon$ is a square at $\mathfrak q$ and at $\mathfrak q'$, and
(ii) an $S$-unit $\delta$ is a square at $\mathfrak q$ if and only if it is a square at $\mathfrak q'$. -/
@[kb "omeara1963" "§65C, 65:20, p. 184 (spots 𝔮 ≠ 𝔮' in S with the same square S-units, ε square at both)"]
theorem exists_twin_spots (T : Finset (HeightOneSpectrum (𝓞 F))) (ε : HN.SUnit (F := F) T) :
    ∃ q q' : HeightOneSpectrum (𝓞 F), q ≠ q' ∧ q ∉ T ∧ q' ∉ T ∧ SqAt q ((ε : Fˣ) : F) ∧ SqAt q' ((ε : Fˣ) : F) ∧
      ∀ δ : HN.SUnit (F := F) T, SqAt q ((δ : Fˣ) : F) ↔ SqAt q' ((δ : Fˣ) : F) := by
  classical
  by_cases hε : IsSquare ((ε : Fˣ) : F)
  · obtain ⟨e, he⟩ := exists_isGenModSq T
    have hpos : 0 < T.card + Fintype.card (InfinitePlace F) := by
      have := Fintype.card_pos (α := InfinitePlace F); omega
    have hns := Sec65DAux.prod_not_isSquare T he {⟨0, hpos⟩} (by simp)
    simp only [Finset.prod_singleton] at hns
    obtain ⟨q, q', hne, hq, hq', -, -, h⟩ := twin_aux T hns
    obtain ⟨r, hr⟩ := hε
    exact ⟨q, q', hne, hq, hq', ⟨algebraMap F _ r, by rw [hr, map_mul]⟩,
      ⟨algebraMap F _ r, by rw [hr, map_mul]⟩, h⟩
  · exact twin_aux T hε

end QuadFormsKB.OMeara
