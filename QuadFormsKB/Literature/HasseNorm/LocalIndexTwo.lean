/-
# The local norm index is exactly 2; the Hilbert symbol is multiplicative at every finite place

For $L = F(\sqrt a)$ and a place $v$ of $F$ non-split in $L$ (i.e. $a$ not a square in $F_v$):

* `isSquare_of_ef_one`: if a prime $w \mid v$ of $L$ has $e = f = 1$, then $a$ is a square in $F_v$
  (so a non-split $v$ has a single prime above it, `eq_of_not_isSquare`, with $ef = 2$);
* `absNorm_pow_ordTwo_eq`: then $N(w)^{\operatorname{ord}_w 2} = N(v)^{2\operatorname{ord}_v 2}$;
* `index_norm_eq_two`: $[F_v^\times : N((F_v \otimes_F L)^\times)] = 2$ at every non-split finite place,
  dyadic places included; `index_norm_eq_two_inf`: the same at a non-split real place;
* `mem_range_norm_iff`: the norm group is $\{x : (a, x)_v = 1\}$;
* `hilbertSymbol_mul_left_finite_nf`: $(ab, c)_v = (a,c)_v (b,c)_v$ for all $a, b, c \in F_v^\times$, i.e. the input
  `NFInputs.hilbertSymbol_mul_left_finite_nf`, proved with the same statement;
* `hmInputs_of`: the Serre-route bundle `NFInputs.HMInputs F` now needs only reciprocity and prescribed symbols
  (the input statement itself is restated in `NumberFieldMain.lean`, downstream of this proof).

**Route** (an elementary count, no Herbrand quotient). With $K = F_v$, $E = K \otimes_F L \cong L_w$
(a field, quadratic over $K$), consider the norm on square classes, $E^\times/E^{\times 2} \to K^\times/K^{\times 2}$:

1. its image is $N(E^\times)/K^{\times 2}$ (squares are norms);
2. its kernel is the image of $K^\times$ (quadratic Hilbert 90, explicitly: if $N(y) = k^2$ and $u = y + k \ne 0$, then
   $y \, N(u) = k u^2$; if $u = 0$, $y = -k$), of size $[K^\times : K^{\times 2}]/2$ since
   $K^\times \cap E^{\times 2} = K^{\times 2} \cup a K^{\times 2}$;
3. the square-class counts $[K^\times : K^{\times 2}] = 4q$, $[E^\times : E^{\times 2}] = 4q^2$ with
   $q = N(v)^{\operatorname{ord}_v 2}$ (`index_sq_completion` for $F$ at $v$ and for $L$ at $w$, using $ef = 2$).

Hence $[N(E^\times) : K^{\times 2}] = 4q^2/2q = 2q$ and $[K^\times : N(E^\times)] = 4q/2q = 2$. The lower bound
$\ge 2$ was `two_le_index_norm` (`LocalNorm.lean`); the new inputs are step 2 and the equality $ef = 2$.

For $ef = 2$: if $v$ had two primes above it, then $e = f = 1$ at $w$, so $\mathcal O_F \to \mathcal O_L / w^n$ is onto
(injective modulo $v^n$ between sets of equal size $N(v)^n$, `exists_approx_pow`); approximating $s = \sqrt a$ $w$-adically
by $c \in F$ gives $v(a/c^2 - 1) < v(4)$, so $a$ is a square in $F_v$ by the local square theorem.

Multiplicativity in the second variable then follows because $x \mapsto (a, x)_v$ is $\pm 1$-valued with fibre over $1$
a subgroup of index $2$ (`Subgroup.mul_mem_iff_of_index_two`), and an arbitrary $c \in F_v^\times$ is a global element
times a square (`exists_global_mul_sq`). At infinite places multiplicativity was already
`NFLocal.hilbertSymbol_mul_left_infinite_nf`.

Locators are from memory and still `[unverified]`.
-/
import QuadFormsKB.Literature.HasseNorm.Main
open Module NumberField IsDedekindDomain WithZero
open scoped nonZeroDivisors
set_option linter.unusedSectionVars false
noncomputable section
namespace QuadFormsKB.HN
variable {F L : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
  [Algebra.IsQuadraticExtension F L]

/-- $w(c) = v(c)^e$ for $c \in \mathcal O_F$, in terms of `intValuation`. -/
lemma intValuation_algebraMap (w : HeightOneSpectrum (𝓞 L)) (c : 𝓞 F) :
    w.intValuation (algebraMap (𝓞 F) (𝓞 L) c) =
      (under (F := F) w).intValuation c ^ w.asIdeal.ramificationIdx (𝓞 F) := by
  have h := valuation_algebraMap (F := F) w (c : F)
  rw [← HeightOneSpectrum.valuation_of_algebraMap (K := L), ← HeightOneSpectrum.valuation_of_algebraMap (K := F)]
  convert h using 2
  rfl

/-- **Residue approximation when $e = f = 1$:** every $y \in \mathcal O_L$ is congruent modulo $w^n$ to some
$c \in \mathcal O_F$ (the map $\mathcal O_F / v^n \to \mathcal O_L / w^n$ is injective between sets of size $N(v)^n$). -/
lemma exists_approx_pow (w : HeightOneSpectrum (𝓞 L))
    (he : w.asIdeal.ramificationIdx (𝓞 F) = 1)
    (hf : (under (F := F) w).asIdeal.inertiaDeg' w.asIdeal = 1) (y : 𝓞 L) (n : ℕ) :
    ∃ c : 𝓞 F, y - algebraMap (𝓞 F) (𝓞 L) c ∈ w.asIdeal ^ n := by
  classical
  set p := (under (F := F) w).asIdeal with hp
  set P := w.asIdeal with hP
  let φ : 𝓞 F →+* 𝓞 L ⧸ P ^ n := (Ideal.Quotient.mk (P ^ n)).comp (algebraMap (𝓞 F) (𝓞 L))
  have hker : RingHom.ker φ = p ^ n := by
    ext c
    rw [RingHom.mem_ker]
    simp only [φ, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    rw [hP, ← HeightOneSpectrum.intValuation_le_pow_iff_mem, hp,
      ← HeightOneSpectrum.intValuation_le_pow_iff_mem, intValuation_algebraMap, he, pow_one]
  have hinj := RingHom.kerLift_injective φ
  have := (under (F := F) w).isMaximal
  have := w.isMaximal
  have hNP : Ideal.absNorm P = Ideal.absNorm p := by
    rw [← Ideal.absNorm_pow_inertiaDeg p P, ← Ideal.inertiaDeg'_eq_inertiaDeg p P, hf, pow_one]
  have hcardL : Nat.card (𝓞 L ⧸ P ^ n) = Ideal.absNorm p ^ n := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, map_pow, hNP]
  have hcardF : Nat.card (𝓞 F ⧸ RingHom.ker φ) = Ideal.absNorm p ^ n := by
    rw [hker, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, map_pow]
  have hp0 : Ideal.absNorm p ≠ 0 :=
    (Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors).mpr (mem_nonZeroDivisors_of_ne_zero (under (F := F) w).ne_bot)
  have : Finite (𝓞 L ⧸ P ^ n) := Nat.finite_of_card_ne_zero (by rw [hcardL]; exact pow_ne_zero _ hp0)
  have hsurj := (hinj.bijective_of_nat_card_le (by rw [hcardL, hcardF])).2
  obtain ⟨c', hc'⟩ := hsurj (Ideal.Quotient.mk _ y)
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c'
  refine ⟨c, ?_⟩
  rw [← Ideal.Quotient.eq]
  rw [← hc']
  rfl


/-- Every nonzero element of $\mathbb Z_{m0}$ exceeds some $\exp(-n)$. -/
lemma exists_exp_lt {z : ℤᵐ⁰} (hz : z ≠ 0) : ∃ n : ℕ, exp (-(n : ℤ)) < z := by
  refine ⟨(log z).natAbs + 1, ?_⟩
  conv_rhs => rw [← exp_log hz]
  rw [exp_lt_exp]; omega

/-- **A prime with $e = f = 1$ makes $a$ a local square:** if $w \mid v$ has $e(w \mid v) = f(w \mid v) = 1$ and
$s \in L$ has $s^2 = a \ne 0$, then $a$ is a square in $F_v$. (Approximate $s$ $w$-adically by $c \in F$ with
$w(s - c) < w(4)\,w(s)$; then $v(a/c^2 - 1) < v(4)$; apply the local square theorem.) -/
@[kb "neukirch1999" "Ch. II, Prop. 8.2 (decomposition of primes) [unverified]"]
theorem isSquare_of_ef_one (w : HeightOneSpectrum (𝓞 L))
    (he : w.asIdeal.ramificationIdx (𝓞 F) = 1)
    (hf : (under (F := F) w).asIdeal.inertiaDeg' w.asIdeal = 1)
    (a : F) (ha : a ≠ 0) (s : L) (hs : s ^ 2 = algebraMap F L a) :
    IsSquare (algebraMap F ((under (F := F) w).adicCompletion F) a) := by
  set W := w.valuation L with hW
  set V := (under (F := F) w).valuation F with hV
  have hWV : ∀ x : F, W (algebraMap F L x) = V x := fun x => by
    rw [hW, valuation_algebraMap, he, pow_one]
  have hs0 : s ≠ 0 := by
    rintro rfl; apply ha
    have : algebraMap F L a = 0 := by rw [← hs]; ring
    exact (map_eq_zero_iff _ (algebraMap F L).injective).mp this
  have happrox : ∀ B : ℤᵐ⁰, B ≠ 0 → ∃ c : F, W (s - algebraMap F L c) < B := by
    intro B hB
    have halg : IsAlgebraic ℤ s := (IsFractionRing.isAlgebraic_iff ℤ ℚ L).mpr (Algebra.IsAlgebraic.isAlgebraic s)
    obtain ⟨m, hm0, hmint⟩ := halg.exists_integral_multiple
    set y : 𝓞 L := ⟨m • s, hmint⟩ with hy
    have hyc : ∀ c' : 𝓞 F, ((y - algebraMap (𝓞 F) (𝓞 L) c' : 𝓞 L) : L) = (m : L) * s - algebraMap F L c' := by
      intro c'
      simp [y, zsmul_eq_mul]
      rfl
    have hmL : (m : L) ≠ 0 := by exact_mod_cast hm0
    have hWm : W (m : L) ≠ 0 := by rw [ne_eq, Valuation.zero_iff]; exact hmL
    obtain ⟨n, hn⟩ := exists_exp_lt (mul_ne_zero hB hWm)
    obtain ⟨c, hc⟩ := exists_approx_pow w he hf y n
    refine ⟨(c : F) / m, ?_⟩
    have h1 : W (((y - algebraMap (𝓞 F) (𝓞 L) c : 𝓞 L) : L)) ≤ exp (-(n : ℤ)) := by
      rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem] at hc
      rw [hW, HeightOneSpectrum.valuation_of_algebraMap]; exact hc
    have h2 : s - algebraMap F L ((c : F) / m) =
        ((y - algebraMap (𝓞 F) (𝓞 L) c : 𝓞 L) : L) / (m : L) := by
      rw [eq_div_iff hmL, hyc c, map_div₀, map_intCast]
      field_simp
    rw [h2, map_div₀, div_lt_iff₀ (zero_lt_iff.mpr hWm)]
    exact lt_of_le_of_lt h1 hn
  have h4 : W (4 : L) ≠ 0 := by rw [ne_eq, Valuation.zero_iff]; norm_num
  have hWs : W s ≠ 0 := by rw [ne_eq, Valuation.zero_iff]; exact hs0
  obtain ⟨c, hc⟩ := happrox (W 4 * W s) (mul_ne_zero h4 hWs)
  have hW4 : W (4 : L) ≤ 1 := by
    have := HeightOneSpectrum.valuation_le_one (K := L) w (4 : 𝓞 L)
    rw [hW]; exact_mod_cast this
  have hlt : W (s - algebraMap F L c) < W s :=
    lt_of_lt_of_le hc (by simpa using mul_le_mul_left hW4 (W s))
  have hWc : W (algebraMap F L c) = W s := by
    have := Valuation.map_sub_eq_of_lt_right W hlt
    rwa [sub_sub_cancel_left, Valuation.map_neg] at this
  have hsum : W (s + algebraMap F L c) ≤ W s := (W.map_add _ _).trans (by rw [hWc, max_self])
  have hc0 : c ≠ 0 := by
    rintro rfl; rw [map_zero, Valuation.map_zero] at hWc; exact hWs hWc.symm
  have hprod : W (algebraMap F L (a - c ^ 2)) < W 4 * W (algebraMap F L (c ^ 2)) := by
    have : algebraMap F L (a - c ^ 2) = (s - algebraMap F L c) * (s + algebraMap F L c) := by
      rw [map_sub, ← hs, map_pow]; ring
    rw [this, map_mul, map_pow, map_pow, hWc]
    calc W (s - algebraMap F L c) * W (s + algebraMap F L c) ≤ W (s - algebraMap F L c) * W s :=
          mul_le_mul_right hsum _
      _ < (W 4 * W s) * W s := mul_lt_mul_of_pos_right hc (zero_lt_iff.mpr hWs)
      _ = W 4 * W s ^ 2 := by rw [mul_assoc, sq]
  have hkey : V (a / c ^ 2 - 1) < V 4 := by
    have h4' : W (4 : L) = V 4 := by rw [← hWV, map_ofNat (algebraMap F L) 4]
    have : a / c ^ 2 - 1 = (a - c ^ 2) / c ^ 2 := by field_simp
    rw [this, map_div₀, ← hWV, ← hWV, ← h4', div_lt_iff₀]
    · exact hprod
    · rw [zero_lt_iff, ne_eq, Valuation.zero_iff]; simpa using hc0
  set Kv := (under (F := F) w).adicCompletion F
  have hsq := isSquare_of_valued_sub_one_lt (under (F := F) w) (algebraMap F Kv (a / c ^ 2)) (by
    rw [← map_one (algebraMap F Kv), ← map_sub, valued_algebraMap,
      show (4 : Kv) = algebraMap F Kv 4 by rw [map_ofNat], valued_algebraMap]
    exact hkey)
  obtain ⟨r, hr⟩ := hsq
  refine ⟨r * algebraMap F Kv c, ?_⟩
  have : a = a / c ^ 2 * c ^ 2 := by field_simp
  rw [this, map_mul, hr, map_pow]; ring

/-- **Non-split places have one prime above:** if $a$ is not a square in $F_v$, $w$ is the only prime of $L$
over $v$. -/
lemma eq_of_not_isSquare (a : F) (ha : a ≠ 0) (s : L) (hs : s ^ 2 = algebraMap F L a)
    (w : HeightOneSpectrum (𝓞 L))
    (hv : ¬ IsSquare (algebraMap F ((under (F := F) w).adicCompletion F) a))
    (w' : HeightOneSpectrum (𝓞 L)) (h : under (F := F) w' = under w) : w' = w := by
  by_contra hne
  obtain ⟨he, hf⟩ := ef_of_two (F := F) w' w hne h
  rw [ramificationIdx'_eq] at he
  apply hv; rw [← h]; exact isSquare_of_ef_one w' he hf a ha s hs

/-- At a non-split place, $N(w)^{\operatorname{ord}_w 2} = N(v)^{2\operatorname{ord}_v 2}$ (as $ef = 2$). -/
lemma absNorm_pow_ordTwo_eq (a : F) (ha : a ≠ 0) (s : L) (hs : s ^ 2 = algebraMap F L a)
    (w : HeightOneSpectrum (𝓞 L))
    (hv : ¬ IsSquare (algebraMap F ((under (F := F) w).adicCompletion F) a)) :
    Ideal.absNorm w.asIdeal ^ ordTwo w =
      Ideal.absNorm (under (F := F) w).asIdeal ^ (2 * ordTwo (under (F := F) w)) := by
  classical
  have hef := ef_of_unique (F := F) w (eq_of_not_isSquare a ha s hs w hv)
  have := (under (F := F) w).isMaximal
  have := w.isMaximal
  have hf : (under (F := F) w).asIdeal.inertiaDeg' w.asIdeal = w.asIdeal.inertiaDeg (𝓞 F) :=
    Ideal.inertiaDeg'_eq_inertiaDeg _ _
  have hN : Ideal.absNorm w.asIdeal =
      Ideal.absNorm (under (F := F) w).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 F) :=
    (Ideal.absNorm_pow_inertiaDeg (under (F := F) w).asIdeal w.asIdeal).symm
  rw [ramificationIdx'_eq (F := F), hf] at hef
  rw [hN, ordTwo_liesOver (F := F), ← pow_mul]
  congr 1
  calc w.asIdeal.inertiaDeg (𝓞 F) * (w.asIdeal.ramificationIdx (𝓞 F) * ordTwo (under (F := F) w))
      = (w.asIdeal.ramificationIdx (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 F)) * ordTwo (under (F := F) w) := by ring
    _ = 2 * ordTwo (under (F := F) w) := by rw [hef]

section D2

attribute [local instance] compAlgebra

open scoped TensorProduct

/-- **The local norm index at a non-split finite place is exactly $2$** ($a$ not a square in $F_v$, any
residue characteristic, dyadic included): $[F_v^\times : N((F_v \otimes_F L)^\times)] = 2$.

*Proof.* As for `two_le_index_norm`, plus: the preimage of $F_v^{\times 2}$ under the norm is
$F_v^\times E^{\times 2}$ (quadratic Hilbert 90 in the explicit form $y\,N(y + k) = k\,(y + k)^2$ when $N(y) = k^2$),
and $[E^\times : E^{\times 2}] = 4q^2$ exactly (`absNorm_pow_ordTwo_eq`). Then
$[E^\times : F_v^\times E^{\times 2}] = 4q^2 / 2q = 2q = [N E^\times : F_v^{\times 2}]$ and the index is $4q / 2q = 2$. -/
@[kb "milne2020cft" "Ch. III §2 (local norm index, n = 2) [unverified]"]
theorem index_norm_eq_two (a : F) (hd : ¬ IsSquare a) (s : L) (hs : s ^ 2 = algebraMap F L a)
    (hspan : ∀ y : L, ∃ b₀ b₁ : F, y = algebraMap F L b₀ + algebraMap F L b₁ * s)
    (w : HeightOneSpectrum (𝓞 L))
    (hv : ¬ IsSquare (algebraMap F (HeightOneSpectrum.adicCompletion F (under (F := F) w)) a)) :
    (Units.map (Algebra.norm (HeightOneSpectrum.adicCompletion F (under (F := F) w)) :
      (HeightOneSpectrum.adicCompletion F (under (F := F) w)) ⊗[F] L →*
        HeightOneSpectrum.adicCompletion F (under (F := F) w))).range.index = 2 := by
  classical
  have ha0 : a ≠ 0 := by rintro rfl; exact hd ⟨0, by simp⟩
  set Fv := HeightOneSpectrum.adicCompletion F (under (F := F) w)
  set E := Fv ⊗[F] L
  obtain ⟨t, -, ht2, hspanT, huniqT, hnormT, hrank⟩ := tensor_structure a hd s hs hspan Fv
  set α := algebraMap F Fv a with hα
  -- every nonzero element of E is a unit
  have hunit : ∀ y : E, y ≠ 0 → IsUnit y := by
    intro y hy
    obtain ⟨x₀, x₁, rfl⟩ := hspanT y
    have hN : x₀ ^ 2 - α * x₁ ^ 2 ≠ 0 := by
      intro h0
      by_cases hx1 : x₁ = 0
      · subst hx1
        have : x₀ = 0 := by simpa using h0
        subst this; simp at hy
      · apply hv
        refine ⟨x₀ / x₁, ?_⟩
        rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hx1 hx1)]
        linear_combination -h0
    have hmul : (algebraMap Fv E x₀ + algebraMap Fv E x₁ * t) *
        (algebraMap Fv E (x₀ ^ 2 - α * x₁ ^ 2)⁻¹ *
          (algebraMap Fv E x₀ - algebraMap Fv E x₁ * t)) = 1 := by
      have h1 : algebraMap Fv E (x₀ ^ 2 - α * x₁ ^ 2)⁻¹ * algebraMap Fv E (x₀ ^ 2 - α * x₁ ^ 2) = 1 := by
        rw [← map_mul, inv_mul_cancel₀ hN, map_one]
      have h2 : (algebraMap Fv E x₀ + algebraMap Fv E x₁ * t) *
          (algebraMap Fv E x₀ - algebraMap Fv E x₁ * t) = algebraMap Fv E (x₀ ^ 2 - α * x₁ ^ 2) := by
        rw [map_sub, map_mul, map_pow, map_pow]
        linear_combination (-(algebraMap Fv E x₁) ^ 2) * ht2
      calc _ = algebraMap Fv E (x₀ ^ 2 - α * x₁ ^ 2)⁻¹ * ((algebraMap Fv E x₀ + algebraMap Fv E x₁ * t) *
          (algebraMap Fv E x₀ - algebraMap Fv E x₁ * t)) := by ring
        _ = 1 := by rw [h2, h1]
    exact IsUnit.of_mul_eq_one _ hmul
  set Lw := HeightOneSpectrum.adicCompletion L w
  have hΦinj : Function.Injective (tensorToCompletion (F := F) w) := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    by_contra hy0
    obtain ⟨u, rfl⟩ := hunit y hy0
    have hu := (Units.map (tensorToCompletion (F := F) w : E →* Lw) u).ne_zero
    exact hu hy
  set eE : E ≃ₐ[Fv] Lw := AlgEquiv.ofBijective _ ⟨hΦinj, tensorToCompletion_surjective w⟩
  -- squares in E
  have hSqE : (powMonoidHom 2 : Eˣ →* Eˣ).range.index =
      4 * Ideal.absNorm (under (F := F) w).asIdeal ^ (2 * ordTwo (under (F := F) w)) := by
    have hmap : (powMonoidHom 2 : Eˣ →* Eˣ).range.map (Units.mapEquiv eE.toMulEquiv).toMonoidHom =
        (powMonoidHom 2 : Lwˣ →* Lwˣ).range := by
      ext z
      constructor
      · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
        exact ⟨Units.mapEquiv eE.toMulEquiv y, by simp⟩
      · rintro ⟨y, rfl⟩
        refine ⟨(Units.mapEquiv eE.toMulEquiv).symm y ^ 2, ⟨_, rfl⟩, ?_⟩
        simp only [powMonoidHom_apply, MulEquiv.coe_toMonoidHom, map_pow, MulEquiv.apply_symm_apply]
    have := Subgroup.index_map_equiv (powMonoidHom 2 : Eˣ →* Eˣ).range (Units.mapEquiv eE.toMulEquiv)
    rw [← this]
    erw [hmap]
    rw [index_sq_completion (K := L) w]
    rw [absNorm_pow_ordTwo_eq a ha0 s hs w hv]
  have hSqE0 : (powMonoidHom 2 : Eˣ →* Eˣ).range.index ≠ 0 := by
    have hmap : (powMonoidHom 2 : Eˣ →* Eˣ).range.map (Units.mapEquiv eE.toMulEquiv).toMonoidHom =
        (powMonoidHom 2 : Lwˣ →* Lwˣ).range := by
      ext z
      constructor
      · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
        exact ⟨Units.mapEquiv eE.toMulEquiv y, by simp⟩
      · rintro ⟨y, rfl⟩
        refine ⟨(Units.mapEquiv eE.toMulEquiv).symm y ^ 2, ⟨_, rfl⟩, ?_⟩
        simp only [powMonoidHom_apply, MulEquiv.coe_toMonoidHom, map_pow, MulEquiv.apply_symm_apply]
    have := Subgroup.index_map_equiv (powMonoidHom 2 : Eˣ →* Eˣ).range (Units.mapEquiv eE.toMulEquiv)
    rw [← this]
    erw [hmap]
    rw [index_sq_completion (K := L) w]
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ ((Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors).mpr
      (mem_nonZeroDivisors_of_ne_zero w.ne_bot)))
  -- the counting
  set q := Ideal.absNorm (under (F := F) w).asIdeal ^ ordTwo (under (F := F) w) with hq
  have hq0 : 0 < q := pow_pos (Nat.pos_of_ne_zero ((Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors).mpr
      (mem_nonZeroDivisors_of_ne_zero (under (F := F) w).ne_bot))) _
  have hSqE' : (powMonoidHom 2 : Eˣ →* Eˣ).range.index = 4 * q ^ 2 := by
    rw [hq, ← pow_mul, mul_comm (ordTwo _) 2]; exact hSqE
  have hSqF : (powMonoidHom 2 : Fvˣ →* Fvˣ).range.index = 4 * q := index_sq_completion _
  set Nm : Eˣ →* Fvˣ := Units.map (Algebra.norm Fv : E →* Fv)
  set incl : Fvˣ →* Eˣ := Units.map (algebraMap Fv E : Fv →* E)
  set SqF := (powMonoidHom 2 : Fvˣ →* Fvˣ).range
  set SqE := (powMonoidHom 2 : Eˣ →* Eˣ).range
  have hNincl : ∀ c : Fvˣ, Nm (incl c) = c ^ 2 := by
    intro c; ext
    simp only [Nm, incl, Units.coe_map, MonoidHom.coe_ofClass, Units.val_pow_eq_pow_val]
    rw [Algebra.norm_algebraMap, hrank]
  have hSqF_le : SqF ≤ Nm.range := by
    rintro _ ⟨c, rfl⟩; exact ⟨incl c, hNincl c⟩
  set M := incl.range ⊔ SqE
  have hM : M ≤ SqF.comap Nm := by
    rw [sup_le_iff]; constructor
    · rintro _ ⟨c, rfl⟩; exact ⟨c, (hNincl c).symm⟩
    · rintro _ ⟨y, rfl⟩; exact ⟨Nm y, by simp⟩
  -- the kernel of the norm modulo squares (quadratic Hilbert 90)
  have hcomap : SqF.comap Nm ≤ M := by
    rintro y ⟨k, hk⟩
    obtain ⟨x₀, x₁, hyx⟩ := hspanT (y : E)
    have hk' : ((k : Fv)) ^ 2 = x₀ ^ 2 - α * x₁ ^ 2 := by
      have := congrArg Units.val hk
      simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Nm, Units.coe_map] at this
      rw [this, hyx, hnormT]
    by_cases hu : (y : E) + algebraMap Fv E (k : Fv) = 0
    · apply (le_sup_left : incl.range ≤ M)
      refine ⟨-k, ?_⟩
      apply Units.ext
      simp only [incl, Units.coe_map, MonoidHom.coe_ofClass, Units.val_neg, map_neg]
      linear_combination -hu
    · obtain ⟨uu, huu⟩ := hunit _ hu
      have hNu : Algebra.norm Fv ((y : E) + algebraMap Fv E (k : Fv)) =
          (x₀ + (k : Fv)) ^ 2 - α * x₁ ^ 2 := by
        have : (y : E) + algebraMap Fv E (k : Fv) =
            algebraMap Fv E (x₀ + (k : Fv)) + algebraMap Fv E x₁ * t := by rw [hyx, map_add]; ring
        rw [this, hnormT]
      set N := (x₀ + (k : Fv)) ^ 2 - α * x₁ ^ 2 with hN
      have hN0 : N ≠ 0 := by
        rw [← hNu, ← huu]
        exact (Units.map (Algebra.norm Fv : E →* Fv) uu).ne_zero
      have hR := congrArg (algebraMap Fv E) hk'
      simp only [map_pow, map_sub, map_mul] at hR
      have hid : (y : E) * algebraMap Fv E N =
          algebraMap Fv E (k : Fv) * ((y : E) + algebraMap Fv E (k : Fv)) ^ 2 := by
        rw [hN, hyx]
        simp only [map_pow, map_sub, map_mul, map_add]
        linear_combination (-(algebraMap Fv E x₀ + algebraMap Fv E (k : Fv) +
          algebraMap Fv E x₁ * t)) * hR + (-(algebraMap Fv E (k : Fv) * algebraMap Fv E x₁ ^ 2)) * ht2
      have hinv : algebraMap Fv E N * algebraMap Fv E N⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ hN0, map_one]
      have hmem : y = incl (k * (Units.mk0 N hN0)⁻¹) * uu ^ 2 := by
        apply Units.ext
        simp only [incl, Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass, Units.val_inv_eq_inv_val,
          Units.val_mk0, Units.val_pow_eq_pow_val, map_mul, huu]
        linear_combination (algebraMap Fv E N⁻¹) * hid - (y : E) * hinv
      rw [hmem]
      exact M.mul_mem ((le_sup_left : incl.range ≤ M) ⟨_, rfl⟩)
        ((le_sup_right : SqE ≤ M) ⟨uu, rfl⟩)
  -- C := preimage of the squares of E
  set C := SqE.comap incl
  have hSqFC : SqF ≤ C := by
    rintro _ ⟨c, rfl⟩; exact ⟨incl c, by simp⟩
  have hα0 : α ≠ 0 := by
    intro h; apply hv; rw [h]; exact ⟨0, by simp⟩
  set aU : Fvˣ := Units.mk0 α hα0
  have haC : aU ∈ C := by
    have ht0 : t ≠ 0 := by
      intro h; rw [h, zero_mul] at ht2
      exact hα0 ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective Fv E)).mp ht2.symm)
    obtain ⟨tu, htu⟩ := hunit t ht0
    refine ⟨tu, ?_⟩
    ext; simp [incl, aU, htu, pow_two, ht2]
    rfl
  have haSq : aU ∉ SqF := by
    rintro ⟨c, hc⟩; apply hv
    refine ⟨(c : Fv), ?_⟩
    have := congrArg Units.val hc
    simpa [aU, pow_two, ← hα] using this.symm
  have hCidx : SqF.relIndex C = 2 := by
    rw [Subgroup.relIndex]
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨aU, haC⟩, fun b => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    -- b ∈ C : b = y^2 in E
    obtain ⟨y, hy⟩ := b.2
    obtain ⟨x₀, x₁, hyx⟩ := hspanT (y : E)
    have hyb : (algebraMap Fv E x₀ + algebraMap Fv E x₁ * t) ^ 2 = algebraMap Fv E ((b : Fvˣ) : Fv) := by
      have := congrArg Units.val hy
      simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, incl, Units.coe_map, MonoidHom.coe_ofClass] at this
      rw [← hyx, this]
    have hexp : algebraMap Fv E (x₀ ^ 2 + α * x₁ ^ 2 - ((b : Fvˣ) : Fv)) +
        algebraMap Fv E (2 * x₀ * x₁) * t = 0 := by
      rw [map_sub, ← hyb]
      simp only [map_add, map_mul, map_pow, map_ofNat]
      linear_combination (-(algebraMap Fv E x₁) ^ 2) * ht2
    obtain ⟨h1, h2⟩ := huniqT _ _ hexp
    have h2' : x₀ = 0 ∨ x₁ = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact Or.inl (by simpa using h)
      · exact Or.inr h
    have hbval : ((b : Fvˣ) : Fv) = x₀ ^ 2 + α * x₁ ^ 2 := by linear_combination -h1
    have hsqiff : ∀ c : Fvˣ, c ∈ SqF ↔ IsSquare (c : Fv) := by
      intro c
      constructor
      · rintro ⟨d, rfl⟩; exact ⟨d, by simp [pow_two]⟩
      · rintro ⟨r, hr⟩
        have hr0 : r ≠ 0 := by rintro rfl; simp at hr
        exact ⟨Units.mk0 r hr0, by ext; simp [pow_two, hr]⟩
    have hmulval : (((b * ⟨aU, haC⟩ : C) : Fvˣ) : Fv) = ((b : Fvˣ) : Fv) * α := by
      simp [aU]
    rw [hsqiff, hsqiff, hmulval]
    have hb0 : ((b : Fvˣ) : Fv) ≠ 0 := Units.ne_zero _
    have hnot : ¬ (IsSquare (((b : Fvˣ) : Fv) * α) ∧ IsSquare ((b : Fvˣ) : Fv)) := by
      rintro ⟨⟨r₁, h₁⟩, ⟨r₂, h₂⟩⟩
      apply hv
      have hr2 : r₂ ≠ 0 := by rintro rfl; simp at h₂
      refine ⟨r₁ / r₂, ?_⟩
      rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hr2 hr2), ← h₂, ← h₁]; ring
    rcases h2' with h0 | h0
    · -- b = α x₁^2
      subst h0
      have : IsSquare (((b : Fvˣ) : Fv) * α) := ⟨α * x₁, by rw [hbval]; ring⟩
      exact xor_iff_iff_not.mpr ⟨fun _ => fun h => hnot ⟨this, h⟩, fun _ => this⟩
    · subst h0
      have : IsSquare ((b : Fvˣ) : Fv) := ⟨x₀, by rw [hbval]; ring⟩
      rw [_root_.xor_comm]
      exact xor_iff_iff_not.mpr ⟨fun _ => fun h => hnot ⟨h, this⟩, fun _ => this⟩
  have hA := Subgroup.relIndex_mul_index hSqF_le
  have hB : SqF.relIndex Nm.range = (SqF.comap Nm).index := relIndex_range_eq_index_comap_mul Nm SqF
  have hMeq : SqF.comap Nm = M := le_antisymm hcomap hM
  have hD := Subgroup.relIndex_mul_index (le_sup_right : SqE ≤ M)
  have hE : SqE.relIndex M = C.index := by
    rw [Subgroup.relIndex_sup_right, relIndex_range_eq_index_comap_mul]
  have hF := Subgroup.relIndex_mul_index hSqFC
  rw [hCidx, hSqF] at hF
  rw [hE] at hD
  rw [hB, hSqF, hMeq] at hA
  have hCi : C.index = 2 * q := by omega
  rw [hCi, hSqE'] at hD
  have hMi : M.index = 2 * q := by
    have : 2 * q * M.index = 2 * q * (2 * q) := by rw [hD]; ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  rw [hMi] at hA
  have : 2 * q * Nm.range.index = 2 * q * 2 := by rw [hA]; ring
  exact Nat.eq_of_mul_eq_mul_left (by omega) this

end D2

/-- **Hilbert symbol and norms from $K(\sqrt\alpha)$:** in a field with $2 \ne 0$, for $\alpha \ne 0$ and any $x$,
$(\alpha, x)_K = 1$ iff $x = x_0^2 - \alpha x_1^2$ for some $x_0, x_1 \in K$. -/
lemma hilbertSymbol_eq_one_iff_norm (K : Type*) [Field K] (h2 : (2 : K) ≠ 0) {α x : K}
    (hα : α ≠ 0) :
    hilbertSymbol K α x = 1 ↔ ∃ x₀ x₁ : K, x = x₀ ^ 2 - α * x₁ ^ 2 := by
  refine ⟨fun h => ?_, fun ⟨x₀, x₁, h⟩ => hilbertSymbol_eq_one_of_norm K α x x₀ x₁ h⟩
  unfold hilbertSymbol at h
  split_ifs at h with hex
  all_goals try norm_num at h
  obtain ⟨X, Y, Z, hne, hZ⟩ := hex
  by_cases hY : Y = 0
  · subst hY
    have hX0 : X ≠ 0 := by
      rintro rfl
      simp at hZ
      exact hne (by simp [hZ])
    have hZ0 : Z ≠ 0 := by
      rintro rfl
      simp at hZ
      rcases hZ with h | h
      · exact hα h
      · exact hX0 h
    have h1 : α * (X / Z) ^ 2 = 1 := by
      field_simp
      linear_combination -hZ
    refine ⟨(1 + x) / 2, (x - 1) / 2 * (X / Z), ?_⟩
    have h2' : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2
    linear_combination ((x - 1) / 2) ^ 2 * h1 - x * ((2 : K)⁻¹ * 2 + 1) * h2'
  · refine ⟨Z / Y, X / Y, ?_⟩
    field_simp
    linear_combination -hZ

/-- A Hilbert symbol is $\pm 1$. -/
lemma hilbertSymbol_eq_one_or (K : Type*) [Field K] (a b : K) :
    hilbertSymbol K a b = 1 ∨ hilbertSymbol K a b = -1 := by
  unfold hilbertSymbol; split_ifs <;> simp

section D3

attribute [local instance] compAlgebra

open scoped TensorProduct

/-- **The local norm group is the kernel of $(a, \cdot)_v$:** for $x \in F_v^\times$, $x$ is a norm from
$F_v \otimes_F F(\sqrt a)$ iff $(a, x)_v = 1$. -/
@[kb "serre1973" "Ch. III §1.1, Prop. 1 [unverified]"]
lemma mem_range_norm_iff (a : F) (hd : ¬ IsSquare a) (s : L) (hs : s ^ 2 = algebraMap F L a)
    (hspan : ∀ y : L, ∃ b₀ b₁ : F, y = algebraMap F L b₀ + algebraMap F L b₁ * s)
    (w : HeightOneSpectrum (𝓞 L))
    (x : (HeightOneSpectrum.adicCompletion F (under (F := F) w))ˣ) :
    x ∈ (Units.map (Algebra.norm (HeightOneSpectrum.adicCompletion F (under (F := F) w)) :
      (HeightOneSpectrum.adicCompletion F (under (F := F) w)) ⊗[F] L →*
        HeightOneSpectrum.adicCompletion F (under (F := F) w))).range ↔
      hilbertSymbol _ (algebraMap F (HeightOneSpectrum.adicCompletion F (under (F := F) w)) a)
        (x : HeightOneSpectrum.adicCompletion F (under (F := F) w)) = 1 := by
  set Fv := HeightOneSpectrum.adicCompletion F (under (F := F) w)
  set E := Fv ⊗[F] L
  obtain ⟨t, -, ht2, hspanT, -, hnormT, -⟩ := tensor_structure a hd s hs hspan Fv
  have ha0 : a ≠ 0 := by rintro rfl; exact hd ⟨0, by simp⟩
  have hα0 : algebraMap F Fv a ≠ 0 := (map_ne_zero_iff _ (algebraMap F Fv).injective).mpr ha0
  rw [hilbertSymbol_eq_one_iff_norm Fv two_ne_zero hα0]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨x₀, x₁, hyx⟩ := hspanT (y : E)
    refine ⟨x₀, x₁, ?_⟩
    have := congrArg Units.val hy
    simp only [Units.coe_map] at this
    rw [← this, hyx, hnormT]
  · rintro ⟨x₀, x₁, hx⟩
    have hx0 := x.ne_zero
    have hmul : (algebraMap Fv E x₀ + algebraMap Fv E x₁ * t) *
        (algebraMap Fv E (x : Fv)⁻¹ * (algebraMap Fv E x₀ - algebraMap Fv E x₁ * t)) = 1 := by
      have h1 : algebraMap Fv E (x : Fv)⁻¹ * algebraMap Fv E (x : Fv) = 1 := by
        rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
      have h2 := congrArg (algebraMap Fv E) hx
      simp only [map_sub, map_mul, map_pow] at h2
      linear_combination (-(algebraMap Fv E (x : Fv)⁻¹ * (algebraMap Fv E x₁) ^ 2)) * ht2 +
        (-(algebraMap Fv E (x : Fv)⁻¹)) * h2 + h1
    refine ⟨Units.mkOfMulEqOne _ _ hmul, ?_⟩
    apply Units.ext
    simp only [Units.coe_map, Units.val_mkOfMulEqOne]
    rw [hnormT, ← hx]

/-- **$(a, \cdot)_v$ is multiplicative** at a finite place $v$ non-split in $F(\sqrt a)$, $a \in F$ (from
`index_norm_eq_two` and `mem_range_norm_iff`). -/
@[kb "omeara1963" "§63 [unverified]"]
lemma hilbertSymbol_mul_right_of_global (a : F) (hd : ¬ IsSquare a) (s : L)
    (hs : s ^ 2 = algebraMap F L a)
    (hspan : ∀ y : L, ∃ b₀ b₁ : F, y = algebraMap F L b₀ + algebraMap F L b₁ * s)
    (w : HeightOneSpectrum (𝓞 L))
    (hv : ¬ IsSquare (algebraMap F (HeightOneSpectrum.adicCompletion F (under (F := F) w)) a))
    (x y : HeightOneSpectrum.adicCompletion F (under (F := F) w)) (hx : x ≠ 0) (hy : y ≠ 0) :
    hilbertSymbol _ (algebraMap F _ a) (x * y) =
      hilbertSymbol _ (algebraMap F _ a) x * hilbertSymbol _ (algebraMap F _ a) y := by
  have h2 := index_norm_eq_two a hd s hs hspan w hv
  have hmem := fun z => mem_range_norm_iff a hd s hs hspan w z
  have key := Subgroup.mul_mem_iff_of_index_two h2 (a := Units.mk0 x hx) (b := Units.mk0 y hy)
  rw [hmem, hmem, hmem] at key
  simp only [Units.val_mul, Units.val_mk0] at key
  rcases hilbertSymbol_eq_one_or _ (algebraMap F _ a) x with h1 | h1 <;>
    rcases hilbertSymbol_eq_one_or _ (algebraMap F _ a) y with h3 | h3 <;>
    rcases hilbertSymbol_eq_one_or _ (algebraMap F _ a) (x * y) with h4 | h4 <;>
    simp_all

/-- **The local norm index at a non-split real place is exactly $2$:** if $a$ is not a square in $F_v$
($v \mid \infty$), the norms from $F_v \otimes_F F(\sqrt a)$ have index $2$ in $F_v^\times$. (They contain the
squares, of index $\le 2$ (`index_sq_infinite`), and have index $\ge 2$ (`two_le_index_norm_inf`).) -/
@[kb "serre1973" "Ch. III §1.2, Thm. 1 [unverified]"]
theorem index_norm_eq_two_inf (a : F) (hd : ¬ IsSquare a) (s : L) (hs : s ^ 2 = algebraMap F L a)
    (hspan : ∀ y : L, ∃ b₀ b₁ : F, y = algebraMap F L b₀ + algebraMap F L b₁ * s)
    (v : InfinitePlace F) (hv : ¬ IsSquare (algebraMap F v.Completion a)) :
    (Units.map (Algebra.norm v.Completion : v.Completion ⊗[F] L →* v.Completion)).range.index = 2 := by
  classical
  have h2 := two_le_index_norm_inf a hd s hs hspan v hv
  obtain ⟨t, -, -, -, -, -, hrank⟩ := tensor_structure a hd s hs hspan v.Completion
  set Nm : (v.Completion ⊗[F] L)ˣ →* v.Completionˣ :=
    Units.map (Algebra.norm v.Completion : v.Completion ⊗[F] L →* v.Completion)
  have hle : (powMonoidHom 2 : v.Completionˣ →* v.Completionˣ).range ≤ Nm.range := by
    rintro _ ⟨c, rfl⟩
    refine ⟨Units.map (algebraMap v.Completion (v.Completion ⊗[F] L) : _ →* _) c, ?_⟩
    ext
    simp only [Nm, Units.coe_map, MonoidHom.coe_ofClass, Units.val_pow_eq_pow_val, powMonoidHom_apply]
    rw [Algebra.norm_algebraMap, hrank]
  have hdvd := Subgroup.index_dvd_of_le hle
  have hsq := index_sq_infinite v
  have hsq2 : (powMonoidHom 2 : v.Completionˣ →* v.Completionˣ).range.index ≤ 2 := by
    rw [hsq]; split_ifs <;> norm_num
  have hpos : 0 < (powMonoidHom 2 : v.Completionˣ →* v.Completionˣ).range.index := by
    rw [hsq]; split_ifs <;> norm_num
  have := Nat.le_of_dvd hpos hdvd
  omega

end D3

end QuadFormsKB.HN

namespace QuadFormsKB.HN

variable {F : Type} [Field F] [NumberField F]

/-- Every $c \in F_v^\times$ is a global element times a square. -/
lemma exists_global_mul_sq (v : HeightOneSpectrum (𝓞 F)) (c : v.adicCompletion F) (hc : c ≠ 0) :
    ∃ a : F, a ≠ 0 ∧ ∃ d : v.adicCompletion F, d ≠ 0 ∧ c = algebraMap F _ a * d ^ 2 := by
  have h4c : (0 : ℝ) < ‖(4 : (v.adicCompletion F)) * c‖ := norm_pos_iff.mpr (mul_ne_zero (by norm_num) hc)
  obtain ⟨a, ha⟩ := (HeightOneSpectrum.denseRange_algebraMap F v).exists_dist_lt c h4c
  rw [dist_eq_norm] at ha
  have hlt : Valued.v (c - algebraMap F (v.adicCompletion F) a) < Valued.v ((4 : (v.adicCompletion F)) * c) :=
    (Valued.toNormedField.norm_lt_iff).mp ha
  have h4 : Valued.v (4 : (v.adicCompletion F)) ≤ 1 := by
    rw [show (4 : (v.adicCompletion F)) = algebraMap F (v.adicCompletion F) 4 from
      (map_ofNat _ 4).symm, valued_algebraMap]
    exact_mod_cast HeightOneSpectrum.valuation_le_one v (4 : 𝓞 F)
  have hlt' : Valued.v (c - algebraMap F (v.adicCompletion F) a) < Valued.v c :=
    lt_of_lt_of_le hlt (by rw [map_mul]; exact mul_le_of_le_one_left' h4)
  have hva : Valued.v (algebraMap F (v.adicCompletion F) a) = Valued.v c := by
    have := Valuation.map_sub_eq_of_lt_right _ hlt'
    rwa [sub_sub_cancel_left, Valuation.map_neg] at this
  have hc' : Valued.v c ≠ 0 := by rw [ne_eq, Valuation.zero_iff]; exact hc
  have ha0 : algebraMap F (v.adicCompletion F) a ≠ 0 := by
    intro h; rw [h, Valuation.map_zero] at hva; exact hc' hva.symm
  obtain ⟨d, hd⟩ := isSquare_of_valued_sub_one_lt v (c / algebraMap F (v.adicCompletion F) a) (by
    have : c / algebraMap F (v.adicCompletion F) a - 1 = (c - algebraMap F (v.adicCompletion F) a) / algebraMap F (v.adicCompletion F) a := by
      field_simp
    rw [this, map_div₀, div_lt_iff₀ (zero_lt_iff.mpr (by rw [hva]; exact hc')), hva, ← map_mul]
    exact hlt)
  have hd0 : d ≠ 0 := by
    rintro rfl
    simp only [mul_zero, div_eq_zero_iff] at hd
    exact hd.elim hc ha0
  refine ⟨a, fun h => ha0 (by simp [h]), d, hd0, ?_⟩
  rw [← sq] at hd
  rw [← hd]; field_simp

/-- **The Hilbert symbol at a finite place of a number field is multiplicative** (dyadic places included):
for a nonzero prime $\mathfrak p$ of $\mathcal O_F$ and $a, b, c \in F_{\mathfrak p}^\times$,
$(ab, c)_{\mathfrak p} = (a, c)_{\mathfrak p}\,(b, c)_{\mathfrak p}$. Same statement as the input
`NFInputs.hilbertSymbol_mul_left_finite_nf`, now proved.

*Proof.* By symmetry it is enough to show $x \mapsto (c, x)_{\mathfrak p}$ is multiplicative. If $c$ is a square,
every symbol is $1$. Otherwise $c = a_0 d^2$ with $a_0 \in F$ (`exists_global_mul_sq`: $F$ is dense and
squares are open), and $(c, x) = (a_0, x)$. With $L = F(\sqrt{a_0})$ and $w \mid \mathfrak p$, the kernel of
$x \mapsto (a_0, x)_{\mathfrak p}$ is the norm group of $F_{\mathfrak p} \otimes_F L \cong L_w$
(`mem_range_norm_iff`), which has index exactly $2$ (`index_norm_eq_two`); a $\pm 1$-valued function whose
fibre over $1$ is a subgroup of index $2$ is a homomorphism. -/
@[kb "omeara1963" "§63 [unverified]"]
theorem hilbertSymbol_mul_left_finite_nf (v : HeightOneSpectrum (𝓞 F))
    (a b c : v.adicCompletion F) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    hilbertSymbol (v.adicCompletion F) (a * b) c =
      hilbertSymbol (v.adicCompletion F) a c * hilbertSymbol (v.adicCompletion F) b c := by
  rw [hilbertSymbol_comm _ (a * b), hilbertSymbol_comm _ a, hilbertSymbol_comm _ b]
  by_cases hsq : IsSquare c
  · obtain ⟨r, rfl⟩ := hsq
    have h1 : ∀ x, hilbertSymbol (v.adicCompletion F) (r * r) x = 1 := fun x => by
      unfold hilbertSymbol; exact if_pos ⟨1, 0, r, by simp, by ring⟩
    rw [h1, h1, h1]; norm_num
  obtain ⟨a₀, -, d, hd, rfl⟩ := exists_global_mul_sq v c hc
  rw [hilbertSymbol_mul_sq_left _ _ _ _ hd, hilbertSymbol_mul_sq_left _ _ _ _ hd,
    hilbertSymbol_mul_sq_left _ _ _ _ hd]
  have hv : ¬ IsSquare (algebraMap F (v.adicCompletion F) a₀) :=
    fun h => hsq (h.mul ⟨d, sq d⟩)
  have hd' : ¬ IsSquare a₀ := fun h => hv (h.map _)
  obtain ⟨L, _, _, _, s, hs, hspan⟩ := QuadFormsKB.Lam.exists_quadExt a₀ hd'
  obtain ⟨hQ, -, -, -⟩ := quadData a₀ hd' s hs hspan
  obtain ⟨w, rfl⟩ := exists_over (L := L) v
  exact hilbertSymbol_mul_right_of_global a₀ hd' s hs hspan w hv a b ha hb

end QuadFormsKB.HN

namespace QuadFormsKB.HN

variable {F : Type} [Field F] [NumberField F]

/-- **The Serre-route bundle `NFInputs.HMInputs` from its two remaining inputs.** Of the five inputs, three are
now theorems: squares are local–global (`SqLG.isSquare_iff_everywhere`), the Hasse norm theorem
(`HasseNorm.hilbert_eq_one_of_everywhere`) and multiplicativity of the local symbol at finite places
(`HN.hilbertSymbol_mul_left_finite_nf`). So `HMInputs F` follows from Hilbert reciprocity over $F$
(`hrec`, the field `reciprocity`) and elements with prescribed local symbols (`hpres`, the field
`prescribed_hilbert`) alone. -/
theorem hmInputs_of
    (hrec : ∀ a b : F, a ≠ 0 → b ≠ 0 →
      {v : NFPlace F | v.hilbert a b = -1}.Finite ∧ Even {v : NFPlace F | v.hilbert a b = -1}.ncard)
    (hpres : ∀ {ι : Type} [Fintype ι] (a : ι → F), (∀ i, a i ≠ 0) →
      ∀ ε : ι → NFPlace F → ℤ, (∀ i v, ε i v = 1 ∨ ε i v = -1) →
      {v : NFPlace F | ∃ i, ε i v = -1}.Finite →
      (∀ i, Even {v : NFPlace F | ε i v = -1}.ncard) →
      (∀ v : NFPlace F, v.atPlace fun K _ _ =>
        ∃ x : K, x ≠ 0 ∧ ∀ i, hilbertSymbol K (algebraMap F K (a i)) x = ε i v) →
      ∃ x : F, x ≠ 0 ∧ ∀ i v, v.hilbert (a i) x = ε i v) :
    NFInputs.HMInputs F :=
  ⟨hrec, SqLG.isSquare_iff_everywhere, hpres, HasseNorm.hilbert_eq_one_of_everywhere,
    hilbertSymbol_mul_left_finite_nf⟩

end QuadFormsKB.HN
