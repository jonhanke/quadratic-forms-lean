import QuadFormsKB.Tamagawa.BinaryCMLocalBridge

/-!
# The local factor of the maximal order: split, inert, ramified

**Layer:** as in `BinaryCMLocalBridge.lean`: $\Gamma = (\mathcal O_E)_\mathfrak p = \mathfrak o[\omega]$ (`LocData`), $\psi(x) = (-d, x)_\mathfrak p$ the
local Hilbert symbol.

**Proves**
* `mem_loc_of_integral` (**maximality**): $y \in F_\mathfrak p^2$ with $\mathrm{Tr}(y) = 2y_0$ and $N(y) = y_0^2 + dy_1^2$ in $\mathfrak o$ lies in
  $\Lambda$ (approximate $y$ by a global $x$, clear denominators prime to $\mathfrak p$: $tx$ is integral over $\mathcal O_F$);
* `hensel_quad`: $X^2 - TX + N$ with $T$ a unit and $N \in \mathfrak p$ has a root in $\mathfrak o$ ($\mathfrak o$ is Henselian);
  `two_mul_le_one_of_norm`: if $-d$ is not a square, $N(y) \in \mathfrak o \Rightarrow \mathrm{Tr}(y) \in \mathfrak o$;
* `ψ_eq_one_iff`, `ψ_mul`: $\psi(x) = 1$ iff $x = x_0^2 + dx_1^2$; $\psi$ is multiplicative (`HN.hilbertSymbol_mul_left_finite_nf`).
* `jΓ_split`, `jΓ_inert`, `jΓ_ramified`: the norm index $j(\Gamma) = [\mathfrak o^\times : N(\Gamma^\times)]$ is $1, 1, 2$;
  `card_units_split`, `card_units_inert`, `card_units_ramified`: $|\Gamma_1^\times| = (q-1)^2,\ q^2-1,\ q(q-1)$;
* **`localFactor_maximal`**: $|\Gamma_1^\times|\,j(\Gamma)/(q(q-1)) = 2$ at ramified $\mathfrak p$ and $1 - \chi_{E/F}(\mathfrak p)/q$ otherwise (every prime,
  dyadic included).

Source: Serre 1973, Ch. III §1 (Hilbert symbol) [unverified]; Neukirch 1999, Ch. II §4 (Hensel) [unverified].

-/

open NumberField IsDedekindDomain Matrix WithZero Polynomial

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.BinaryCM

open Lattices QuadForm QuadFormsKB.HilbertModular Binary.Rel BinaryNormOne Loc LocalDensity IsLocalRing

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

variable {D : 𝓞 F} (S : SqrtData D E) (v : HeightOneSpectrum (𝓞 F))

/-- $\mathfrak o_\mathfrak p$ is Henselian (as in `QuatOrder.henselianLocalRing_adicCompletionIntegers`). -/
instance henselian_adicCompletionIntegers' : HenselianLocalRing (v.adicCompletionIntegers F) where
  is_henselian f hf a₀ h₁ h₂ :=
    HenselianRing.is_henselian (I := maximalIdeal (v.adicCompletionIntegers F)) f hf a₀ h₁
      (h₂.map (Ideal.Quotient.mk _))

/-- $d$ in $F_\mathfrak p$. -/
abbrev dv : v.adicCompletion F := dIn D (v.adicCompletion F)

/-- The norm form $N(y) = y_0^2 + dy_1^2$ on $F_\mathfrak p^2$. -/
abbrev Nv (y : Fin 2 → v.adicCompletion F) : v.adicCompletion F := y 0 ^ 2 + dv v (D := D) * y 1 ^ 2

theorem valued_dv_le_one : Valued.v (dv v (D := D)) ≤ 1 := valued_dIn_le_one D v

/-! ### Maximality of $\Lambda$ -/

theorem valued_two_le_one : Valued.v (2 : v.adicCompletion F) ≤ 1 := by
  rw [show (2 : v.adicCompletion F) = algebraMap (𝓞 F) (v.adicCompletion F) 2 from (map_ofNat _ 2).symm]
  exact valued_int_le_one v 2

/-- An element $z \in E$ satisfies $z^2 - \mathrm{Tr}(z)z + N(z) = 0$. -/
theorem sq_sub_trace_add_norm (z : E) :
    z ^ 2 - algebraMap F E (Algebra.trace F E z) * z + algebraMap F E (Algebra.norm F z) = 0 := by
  rw [algebraMap_trace, algebraMap_norm]; ring

/-- **Maximality of $\Lambda = (\mathcal O_E)_\mathfrak p$:** if $2y_0, y_0^2 + dy_1^2 \in \mathfrak o$ then $y \in \Lambda$. -/
theorem mem_loc_of_integral {y : Fin 2 → v.adicCompletion F} (hT : Valued.v (2 * y 0) ≤ 1)
    (hN : Valued.v (Nv v (D := D) y) ≤ 1) : y ∈ loc v (latE S) := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ i, Valued.v (y i) ≤ exp (M : ℤ) := by
    obtain ⟨M0, h0⟩ := exists_valued_le v (y 0)
    obtain ⟨M1, h1⟩ := exists_valued_le v (y 1)
    refine ⟨max M0 M1, fun i => ?_⟩
    fin_cases i
    · exact h0.trans (exp_le_exp.mpr (by omega))
    · exact h1.trans (exp_le_exp.mpr (by omega))
  obtain ⟨x0, hx0⟩ := exists_approx v (y 0) (M : ℤ)
  obtain ⟨x1, hx1⟩ := exists_approx v (y 1) (M : ℤ)
  set x : Fin 2 → F := ![x0, x1]
  set e : Fin 2 → v.adicCompletion F := y - locVec v x
  have he : ∀ i, Valued.v (e i) ≤ exp (-(M : ℤ)) := by
    intro i; fin_cases i
    · exact hx0
    · exact hx1
  have hye : ∀ i, Valued.v (y i * e i) ≤ 1 := fun i => by
    rw [map_mul]
    calc Valued.v (y i) * Valued.v (e i) ≤ exp (M : ℤ) * exp (-(M : ℤ)) := mul_le_mul' (hM i) (he i)
      _ = 1 := by rw [← exp_add]; simp
  have he1 : ∀ i, Valued.v (e i) ≤ 1 := fun i => (he i).trans (by rw [← exp_zero, exp_le_exp]; omega)
  have hxy : locVec v x = y - e := by simp [e]
  -- the global trace and norm of c(x) are v-integral
  have hTx : v.valuation F (2 * x 0) ≤ 1 := by
    rw [← valued_algebraMap]
    have : algebraMap F (v.adicCompletion F) (2 * x 0) = 2 * y 0 - 2 * e 0 := by
      rw [map_mul, map_ofNat, show algebraMap F (v.adicCompletion F) (x 0) = (locVec v x) 0 from rfl, hxy]
      simp; ring
    rw [this]
    refine (Valuation.map_sub _ _ _).trans (max_le hT ?_)
    rw [map_mul]; exact mul_le_one' (valued_two_le_one v) (he1 0)
  have hNx : v.valuation F (x 0 ^ 2 + dF D * x 1 ^ 2) ≤ 1 := by
    rw [← valued_algebraMap]
    have : algebraMap F (v.adicCompletion F) (x 0 ^ 2 + dF D * x 1 ^ 2) =
        Nv v (D := D) y - (2 * (y 0 * e 0) + 2 * dv v (D := D) * (y 1 * e 1)) +
          (e 0 ^ 2 + dv v (D := D) * e 1 ^ 2) := by
      rw [map_add, map_mul, map_pow, map_pow, show algebraMap F (v.adicCompletion F) (x 0) = (locVec v x) 0 from rfl,
        show algebraMap F (v.adicCompletion F) (x 1) = (locVec v x) 1 from rfl, hxy]
      simp only [Pi.sub_apply, Nv, dv, dIn]
      ring
    rw [this]
    refine Valuation.map_add_le _ (Valuation.map_sub_le _ hN (Valuation.map_add_le _ ?_ ?_)) ?_
    · rw [map_mul]; exact mul_le_one' (valued_two_le_one v) (hye 0)
    · rw [map_mul, map_mul]
      exact mul_le_one' (mul_le_one' (valued_two_le_one v) (valued_dv_le_one v)) (hye 1)
    · refine Valuation.map_add_le _ ?_ ?_
      · rw [map_pow]; exact pow_le_one₀ zero_le (he1 0)
      · rw [map_mul, map_pow]; exact mul_le_one' (valued_dv_le_one v) (pow_le_one₀ zero_le (he1 1))
  -- clear denominators prime to 𝔭
  obtain ⟨t, ht, htm⟩ := exists_not_mem_smul_mem_intVec v (x := ![2 * x 0, x 0 ^ 2 + dF D * x 1 ^ 2])
    (fun i => by fin_cases i; exacts [hTx, hNx])
  obtain ⟨T0, hT0⟩ := htm 0
  obtain ⟨N0, hN0⟩ := htm 1
  simp only [Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hT0 hN0
  -- t • x ∈ latE
  have htx : t • x ∈ latE S := by
    rw [mem_latE]
    set z := cE S (t • x)
    have hz : z = algebraMap F E (algebraMap (𝓞 F) F t) * cE S x := cE_smul_int S t x
    have htr : Algebra.trace F E (cE S x) = 2 * x 0 := trace_cE S x
    have hnm : Algebra.norm F (cE S x) = x 0 ^ 2 + dF D * x 1 ^ 2 := norm_cE S x
    -- z² - (t·Tr) z + t²N = 0 with integral coefficients
    have hpoly : z ^ 2 - algebraMap F E (algebraMap (𝓞 F) F T0) * z +
        algebraMap F E (algebraMap (𝓞 F) F (t * N0)) = 0 := by
      have h0 := sq_sub_trace_add_norm (F := F) (cE S x)
      rw [htr, hnm] at h0
      rw [hz, map_mul, hT0, hN0]
      simp only [Algebra.smul_def, map_mul, map_ofNat] at h0 ⊢
      linear_combination (algebraMap F E (algebraMap (𝓞 F) F t)) ^ 2 * h0
    have hmon : (X ^ 2 + C (-T0) * X + C (t * N0) : (𝓞 F)[X]).Monic := by monicity!
    have hint : IsIntegral (𝓞 F) z := by
      refine ⟨_, hmon, ?_⟩
      simp only [eval₂_add, eval₂_mul, eval₂_X_pow, eval₂_C, eval₂_X, eval₂_neg, map_neg]
      rw [IsScalarTower.algebraMap_apply (𝓞 F) F E T0, IsScalarTower.algebraMap_apply (𝓞 F) F E (t * N0)]
      linear_combination hpoly
    exact isIntegral_trans _ hint
  -- t is a unit at 𝔭
  have hlx : locVec v x ∈ loc v (latE S) := by
    have hv : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) t) = 1 := by
      rw [valued_algebraMap_int, HeightOneSpectrum.intValuation_eq_one_iff.mpr ht]
    have hd0 : algebraMap (𝓞 F) (v.adicCompletion F) t ≠ 0 := by
      intro h0; rw [h0, map_zero] at hv; exact zero_ne_one hv
    have hc : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) t)⁻¹ ≤ 1 := by rw [map_inv₀, hv, inv_one]
    have e' : locVec v x = toO v _ hc • locVec v (t • x) := by
      rw [locVec_smul_int, smul_smul]
      have : toO v _ hc * algebraMap (𝓞 F) (v.adicCompletionIntegers F) t = 1 := by
        apply Subtype.ext
        show (algebraMap (𝓞 F) (v.adicCompletion F) t)⁻¹ * algebraMap (𝓞 F) (v.adicCompletion F) t = 1
        exact inv_mul_cancel₀ hd0
      rw [this, one_smul]
    rw [e']
    exact Submodule.smul_mem _ _ (locVec_mem_loc v htx)
  have hey : e ∈ loc v (latE S) := mem_loc_of_mem_std S v (fun i => by simpa using he1 i)
  have : y = locVec v x + e := by rw [hxy]; abel
  rw [this]
  exact Submodule.add_mem _ hlx hey

/-! ### Hensel's lemma for quadratics -/

theorem mem_maximalIdeal_iff_valued (z : v.adicCompletionIntegers F) :
    z ∈ maximalIdeal (v.adicCompletionIntegers F) ↔ Valued.v (z : v.adicCompletion F) < 1 := by
  rw [(NF.irreducible_π v).maximalIdeal_eq, ← pow_one (NF.π v), NF.mem_span_π_pow]
  constructor
  · intro h; exact lt_of_le_of_lt h (by rw [← exp_zero, exp_lt_exp]; omega)
  · intro h
    by_cases hz : (z : v.adicCompletion F) = 0
    · rw [hz, map_zero]; exact zero_le
    obtain ⟨m, hm⟩ := exists_valued_eq_exp v hz
    rw [hm, ← exp_zero, exp_lt_exp] at h
    rw [hm, exp_le_exp]; push_cast; omega

/-- **Hensel:** $X^2 - TX + N$ with $T \in \mathfrak o^\times$ and $N \in \mathfrak p$ has a root in $\mathfrak o$. -/
theorem hensel_quad {T N : v.adicCompletionIntegers F} (hT : IsUnit T)
    (hN : N ∈ maximalIdeal (v.adicCompletionIntegers F)) : ∃ r : v.adicCompletionIntegers F, r ^ 2 - T * r + N = 0 := by
  set f : (v.adicCompletionIntegers F)[X] := X ^ 2 - C T * X + C N
  have hmon : f.Monic := by simp only [f]; monicity!
  obtain ⟨r, hr, -⟩ := HenselianLocalRing.is_henselian f hmon 0 (by simpa [f] using hN) (by
    simp only [f, derivative_add, derivative_sub, derivative_X_pow, derivative_mul, derivative_C, derivative_X]
    simpa using hT.neg)
  refine ⟨r, ?_⟩
  have := hr
  simp only [f, IsRoot, eval_add, eval_sub, eval_pow, eval_mul, eval_C, eval_X] at this
  exact this

/-- **If $-d$ is not a square in $F_\mathfrak p$, $N(y) \in \mathfrak o \Rightarrow \mathrm{Tr}(y) = 2y_0 \in \mathfrak o$** (else $X^2 - \mathrm{Tr}(y)X + N(y)$,
rescaled to $Y^2 - Y + N/\mathrm{Tr}^2$, has a Hensel root and its discriminant $-4dy_1^2$ would be a square). -/
theorem two_mul_le_one_of_norm (hns : ¬ IsSquare (-dv v (D := D))) {y : Fin 2 → v.adicCompletion F}
    (hN : Valued.v (Nv v (D := D) y) ≤ 1) : Valued.v (2 * y 0) ≤ 1 := by
  by_contra hlt
  push Not at hlt
  set T := 2 * y 0
  set N := Nv v (D := D) y
  have hT0 : T ≠ 0 := by intro h0; rw [h0, map_zero] at hlt; exact not_lt.mpr zero_le hlt
  -- ε = N/T² is in the maximal ideal
  have hnT : 1 < ‖T‖ := (Valued.toNormedField.norm_lt_iff (x := (1 : v.adicCompletion F)) (x' := T)).mpr
    (by rw [map_one]; exact hlt) |> fun h => by simpa using h
  have hnN : ‖N‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.mpr hN
  set ε := N / T ^ 2
  have hε : ‖ε‖ < 1 := by
    rw [norm_div, norm_pow, div_lt_one (by positivity)]
    nlinarith
  have hε1 : Valued.v ε ≤ 1 := Valued.toNormedField.norm_le_one_iff.mp hε.le
  set εO : v.adicCompletionIntegers F := toO v ε hε1
  have hεm : εO ∈ maximalIdeal (v.adicCompletionIntegers F) :=
    (mem_maximalIdeal_iff_valued v εO).mpr (Valued.toNormedField.norm_lt_one_iff.mp hε)
  obtain ⟨r, hr⟩ := hensel_quad v isUnit_one hεm
  have hr' : (r : v.adicCompletion F) ^ 2 - r + ε = 0 := by
    have := congrArg Subtype.val hr
    push_cast at this
    rw [one_mul] at this
    exact this
  -- the discriminant -4 d y₁² is a square
  set X0 := T * (r : v.adicCompletion F)
  have hdisc : (2 * X0 - T) ^ 2 = -4 * dv v (D := D) * y 1 ^ 2 := by
    have h1 : X0 ^ 2 - T * X0 + N = 0 := by
      have : X0 ^ 2 - T * X0 + N = T ^ 2 * ((r : v.adicCompletion F) ^ 2 - r + ε) := by
        simp only [X0, ε]; field_simp
      rw [this, hr', mul_zero]
    have hNe : N = y 0 ^ 2 + dv v (D := D) * y 1 ^ 2 := rfl
    linear_combination 4 * h1 - 4 * hNe + (T - 2 * y 0) * (T + 2 * y 0)
  by_cases hy1 : y 1 = 0
  · apply not_le.mpr hlt
    have hN' : N = y 0 ^ 2 := by simp [N, Nv, hy1]
    rw [hN'] at hN
    have hy0 : Valued.v (y 0) ≤ 1 := by
      by_contra h; push Not at h
      rw [map_pow] at hN
      have := one_lt_pow₀ h (two_ne_zero)
      exact not_lt.mpr hN this
    rw [map_mul]; exact mul_le_one' (valued_two_le_one v) hy0
  · apply hns
    refine ⟨(2 * X0 - T) / (2 * y 1), ?_⟩
    have h2 : (2 : v.adicCompletion F) ≠ 0 := two_ne_zero
    field_simp
    linear_combination -hdisc

/-! ### The local Hilbert symbol $\psi = (-d, \cdot)_\mathfrak p$ -/

/-- $\psi(x) = (-d, x)_\mathfrak p$. -/
abbrev ψv (x : v.adicCompletion F) : ℤ := hilbertSymbol (v.adicCompletion F) (-dv v (D := D)) x

include S in
theorem dv_ne_zero : dv v (D := D) ≠ 0 := by
  rw [dv, dIn]
  exact (_root_.map_ne_zero _).mpr ((map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr S.D_ne)

include S in
theorem ψv_eq_one_iff (x : v.adicCompletion F) :
    ψv v (D := D) x = 1 ↔ ∃ x₀ x₁ : v.adicCompletion F, x = x₀ ^ 2 + dv v (D := D) * x₁ ^ 2 := by
  rw [ψv, HN.hilbertSymbol_eq_one_iff_norm _ two_ne_zero (neg_ne_zero.mpr (dv_ne_zero S v))]
  simp only [neg_mul, sub_neg_eq_add]

include S in
theorem ψv_mul {x y : v.adicCompletion F} (hx : x ≠ 0) (hy : y ≠ 0) :
    ψv v (D := D) (x * y) = ψv v (D := D) x * ψv v (D := D) y := by
  rw [ψv, ψv, ψv, hilbertSymbol_comm, hilbertSymbol_comm _ _ x, hilbertSymbol_comm _ _ y]
  exact HN.hilbertSymbol_mul_left_finite_nf v x y _ hx hy (neg_ne_zero.mpr (dv_ne_zero S v))

theorem ψv_eq_one_or (x : v.adicCompletion F) : ψv v (D := D) x = 1 ∨ ψv v (D := D) x = -1 :=
  HN.hilbertSymbol_eq_one_or _ _ _

include S in
theorem ψv_Nv (y : Fin 2 → v.adicCompletion F) : ψv v (D := D) (Nv v (D := D) y) = 1 :=
  (ψv_eq_one_iff S v _).mpr ⟨y 0, y 1, rfl⟩

include S in
theorem ψv_sq {x : v.adicCompletion F} : ψv v (D := D) (x ^ 2) = 1 :=
  (ψv_eq_one_iff S v _).mpr ⟨x, 0, by ring⟩

theorem neg_dv_eq : -dv v (D := D) = algebraMap F (v.adicCompletion F) (-dF D) := by
  rw [map_neg]

include S in
/-- **Split iff $-d$ is a square in $F_\mathfrak p$** (`isSquare_of_split`, `not_isSquare_of_not_split`; every prime). -/
theorem isSquare_neg_dv_iff : IsSquare (-dv v (D := D)) ↔ relChar E v = 1 := by
  have ha : algebraMap F E (-dF D) = S.θ ^ 2 := by rw [S.sq, map_neg]
  rw [neg_dv_eq]
  constructor
  · intro h
    by_contra hne
    exact not_isSquare_of_not_split hne (θ_ne_zero S) S.conj_eq ha h
  · intro h
    exact isSquare_of_split h (neg_ne_zero.mpr (dF_ne_zero S)) ha

include S in
/-- **If $-d$ is not a square, $\psi$ takes the value $-1$** (local nondegeneracy, `SqDual.hilbCl_nondeg_fin`). -/
theorem exists_ψv_neg (h : ¬ IsSquare (-dv v (D := D))) : ∃ x : v.adicCompletion F, x ≠ 0 ∧ ψv v (D := D) x = -1 := by
  have hd0 : -dv v (D := D) ≠ 0 := neg_ne_zero.mpr (dv_ne_zero S v)
  set d : (v.adicCompletion F)ˣ := Units.mk0 _ hd0
  have hy : (QuotientGroup.mk d : SqDual.SqCl (v.adicCompletion F)) ≠ 1 := fun h1 =>
    h ((SqDual.mk_eq_one_iff_isSquare _ d).mp h1)
  obtain ⟨x, hx⟩ := SqDual.hilbCl_nondeg_fin v _ hy
  induction x using QuotientGroup.induction_on with
  | H u =>
    refine ⟨u, u.ne_zero, ?_⟩
    rw [SqDual.hilbCl_mk, hilbertSymbol_comm] at hx
    exact hx

/-! ### Inert and ramified primes -/

theorem valued_unit_eq_one {u : v.adicCompletionIntegers F} (hu : IsUnit u) :
    Valued.v (u : v.adicCompletion F) = 1 := by
  obtain ⟨w, rfl⟩ := hu
  have h1 : ‖((w : v.adicCompletionIntegers F) : v.adicCompletion F)‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp w.1.2)
  have h2 : ‖(((w⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : v.adicCompletion F)‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp w⁻¹.1.2)
  have h3 : ‖((w : v.adicCompletionIntegers F) : v.adicCompletion F)‖ *
      ‖(((w⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : v.adicCompletion F)‖ = 1 := by
    rw [← norm_mul]
    have : ((w : v.adicCompletionIntegers F) : v.adicCompletion F) *
        (((w⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : v.adicCompletion F) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv]; rfl
    rw [this, norm_one]
  refine Valued.toNormedField.norm_eq_one_iff.mp ?_
  nlinarith [norm_nonneg ((w : v.adicCompletionIntegers F) : v.adicCompletion F),
    norm_nonneg (((w⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : v.adicCompletion F)]

include S in
/-- **The genus character is $\psi$:** $\psi_\mathfrak p(x) = (\delta, x)_\mathfrak p = (-D, x)_\mathfrak p$ ($\delta = $ `relD` $= f^2\cdot(-D)$). -/
theorem genusSym_eq_ψv (x : F) :
    genusSym E (NFPlace.finite v) x = ψv v (D := D) (algebraMap F (v.adicCompletion F) x) := by
  have := charZero_top F E
  obtain ⟨f, hf⟩ := (conj_eq_self_iff (F := F) ((relGen F E : E) / S.θ)).mp (by
    rw [map_div₀, conj_relGen, S.conj_eq, neg_div_neg_eq])
  have hθ := θ_ne_zero S
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, div_eq_zero_iff] at hf
    exact hf.elim relGen_ne_zero hθ
  have hg : (relGen F E : E) = algebraMap F E f * S.θ := by rw [hf]; field_simp
  have hrel : relD F E = -dF D * f ^ 2 := by
    apply (algebraMap F E).injective
    rw [algebraMap_relD, hg, mul_pow, S.sq, map_mul, map_neg, map_pow]; ring
  show hilbertSymbol (v.adicCompletion F) (algebraMap F _ (relD F E)) (algebraMap F _ x) = _
  rw [hrel, map_mul, map_pow, map_neg]
  exact HM3.hilbertSymbol_mul_sq_left _ _ _ _ ((_root_.map_ne_zero _).mpr hf0)

theorem valued_sub_lt_four {e k : ℕ}
    (he : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) 4) = WithZero.exp (-(e : ℤ))) (hk : e + 1 ≤ k)
    {z : v.adicCompletion F} (hz : Valued.v z ≤ exp (-(k : ℤ))) :
    Valued.v z < Valued.v (4 : v.adicCompletion F) := by
  rw [show (4 : v.adicCompletion F) = algebraMap (𝓞 F) (v.adicCompletion F) 4 from (map_ofNat _ 4).symm, he]
  exact lt_of_le_of_lt hz (by rw [exp_lt_exp]; omega)

theorem algebraMap_int_eq (a : 𝓞 F) :
    algebraMap (𝓞 F) (v.adicCompletion F) a = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) :=
  IsScalarTower.algebraMap_apply _ _ _ _

theorem πF_eq : πF v = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (NF.unif v)) := by
  rw [← algebraMap_int_eq]; rfl

include S in
/-- **At an inert prime $\psi$ is trivial on units and $\psi(\varpi) = -1$** (`genusSym_inert_iff`, transported to local units by
approximation and the local square theorem). -/
theorem ψv_inert (h : relChar E v = -1) :
    (∀ u : v.adicCompletionIntegers F, IsUnit u → ψv v (D := D) (u : v.adicCompletion F) = 1) ∧
      ψv v (D := D) (πF v) = -1 := by
  obtain ⟨e, he⟩ := exists_valued_four v
  constructor
  · intro u hu
    obtain ⟨a, ha⟩ := exists_approx_int v u (e + 1)
    have hu1 := valued_unit_eq_one v hu
    have hu0 : (u : v.adicCompletion F) ≠ 0 := by intro h0; rw [h0, map_zero] at hu1; exact zero_ne_one hu1
    set a' := algebraMap (𝓞 F) (v.adicCompletion F) a
    have hlt : Valued.v ((u : v.adicCompletion F) - a') < Valued.v (u : v.adicCompletion F) := by
      rw [hu1]; exact lt_of_le_of_lt ha (by rw [← exp_zero, exp_lt_exp]; omega)
    have ha1 : Valued.v a' = 1 := by
      have h' : Valued.v (a' - (u : v.adicCompletion F)) < Valued.v (u : v.adicCompletion F) := by
        rwa [Valuation.map_sub_swap]
      rw [Valuation.map_eq_of_sub_lt _ h', hu1]
    have ha0 : a' ≠ 0 := by intro h0; rw [h0, map_zero] at ha1; exact zero_ne_one ha1
    have hsq : IsSquare (a' / u) := by
      refine HN.isSquare_of_valued_sub_one_lt v _ (valued_sub_lt_four v he le_rfl ?_)
      have : a' / u - 1 = -((u : v.adicCompletion F) - a') / u := by field_simp; ring
      rw [this, map_div₀, Valuation.map_neg, hu1, div_one]; exact ha
    obtain ⟨r, hr⟩ := hsq
    have hr0 : r ≠ 0 := by rintro rfl; rw [mul_zero, div_eq_zero_iff] at hr; exact hr.elim ha0 hu0
    have h1 : ψv v (D := D) a' = ψv v (D := D) (u : v.adicCompletion F) := by
      rw [show a' = (u : v.adicCompletion F) * r ^ 2 by rw [sq, ← hr]; field_simp,
        ψv_mul S v hu0 (pow_ne_zero 2 hr0), ψv_sq S v, mul_one]
    have hav : v.valuation F (algebraMap (𝓞 F) F a) = exp (0 : ℤ) := by
      rw [← valued_algebraMap, ← algebraMap_int_eq, exp_zero]; exact ha1
    have haF : (algebraMap (𝓞 F) F a) ≠ 0 := by
      intro h0; rw [h0, map_zero] at hav; exact exp_ne_zero hav.symm
    have hg := (genusSym_inert_iff h haF hav).mpr ⟨0, rfl⟩
    rw [genusSym_eq_ψv S v, ← algebraMap_int_eq] at hg
    rw [← h1]; exact hg
  · have hval : v.valuation F (algebraMap (𝓞 F) F (NF.unif v)) = exp (-1 : ℤ) := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, NF.intValuation_unif]
    have hu0 : algebraMap (𝓞 F) F (NF.unif v) ≠ 0 := by
      intro h0; rw [h0, map_zero] at hval; exact exp_ne_zero hval.symm
    have hg := genusSym_inert_iff h hu0 hval
    rw [πF_eq, ← genusSym_eq_ψv S v]
    rcases genusSym_eq_one_or (E := E) (NFPlace.finite v) (algebraMap (𝓞 F) F (NF.unif v)) with h1 | h1
    · exact absurd (hg.mp h1) (by decide)
    · exact h1

include S in
/-- **At a ramified prime some element of $\Lambda$ has norm of valuation $1$:** $\Pi \in \mathfrak P \setminus \mathfrak P^2$ for the prime
$\mathfrak P \mid \mathfrak p$ ($\mathfrak p\mathcal O_E = \mathfrak P^2$, $N\mathfrak P = \mathfrak p$) has $v_\mathfrak p(N\Pi) = 1$. -/
theorem exists_mem_loc_valued_Nv_ramified (h : relChar E v = 0) :
    ∃ y ∈ loc v (latE S), Valued.v (Nv v (D := D) y) = exp (-1 : ℤ) := by
  set P := (primeAbove E v).1
  have hP2 : P ^ 2 = v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) := sq_primeAbove h
  have hPne : P ≠ ⊤ := primesOver_ne_top (primeAbove E v)
  have hPbot : P ≠ ⊥ := by
    intro h0
    rw [h0, ← Ideal.zero_eq_bot, zero_pow two_ne_zero, Ideal.zero_eq_bot] at hP2
    exact map_ne_bot v.ne_bot hP2.symm
  -- N(P) = 𝔭
  have hNP : Ideal.relNorm (𝓞 F) P = v.asIdeal := by
    apply ideal_pow_left_injective two_ne_zero
    rw [← map_pow, hP2, relNorm_map]
  -- ϖE ∈ P \ P²
  obtain ⟨ϖE, hwP, hwP2⟩ := IsConcreteLE.exists_of_lt (Ideal.pow_lt_self P hPbot hPne 2 le_rfl)
  have hspan : Ideal.relNorm (𝓞 F) (Ideal.span {ϖE}) = Ideal.span {Algebra.intNorm (𝓞 F) (𝓞 E) ϖE} :=
    Ideal.relNorm_singleton _ _
  have hmem : Algebra.intNorm (𝓞 F) (𝓞 E) ϖE ∈ v.asIdeal := by
    rw [← hNP]
    have := Ideal.relNorm_mono (𝓞 F) ((Ideal.span_singleton_le_iff_mem _).mpr hwP)
    rw [hspan] at this
    exact this (Ideal.mem_span_singleton_self _)
  have hnmem : Algebra.intNorm (𝓞 F) (𝓞 E) ϖE ∉ v.asIdeal ^ 2 := by
    intro h2
    obtain ⟨J, hJ⟩ : P ∣ Ideal.span {ϖE} := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hwP)
    have hrel : Ideal.relNorm (𝓞 F) (Ideal.span {ϖE}) = v.asIdeal * Ideal.relNorm (𝓞 F) J := by
      rw [hJ, map_mul, hNP]
    have hdvd : v.asIdeal * v.asIdeal ∣ v.asIdeal * Ideal.relNorm (𝓞 F) J := by
      rw [← hrel, hspan, ← sq, Ideal.dvd_span_singleton]; exact h2
    have hv0 : v.asIdeal ≠ 0 := by rw [Ne, Ideal.zero_eq_bot]; exact v.ne_bot
    have hdvd' : v.asIdeal ∣ Ideal.relNorm (𝓞 F) J := (mul_dvd_mul_iff_left hv0).mp hdvd
    obtain ⟨P', hP'⟩ := exists_dvd_of_dvd_relNorm v J hdvd'
    rw [eq_primeAbove_of_ramified h P'] at hP'
    apply hwP2
    have : P ^ 2 ∣ Ideal.span {ϖE} := by rw [hJ, sq]; exact mul_dvd_mul_left _ hP'
    exact (Ideal.span_singleton_le_iff_mem _).mp (Ideal.le_of_dvd this)
  have hval : v.intValuation (Algebra.intNorm (𝓞 F) (𝓞 E) ϖE) = exp (-1 : ℤ) := by
    have h1 := (v.intValuation_le_pow_iff_mem _ 1).mpr (by rwa [pow_one])
    have h2 := mt (v.intValuation_le_pow_iff_mem _ 2).mp hnmem
    have h0 : v.intValuation (Algebra.intNorm (𝓞 F) (𝓞 E) ϖE) ≠ 0 := by
      intro h0; rw [h0] at h2; exact h2 zero_le
    obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.mp h0
    rw [← ha] at h1 h2 ⊢
    have h1' : Multiplicative.toAdd a ≤ -1 := by
      have := h1; rw [show (a : ℤᵐ⁰) = exp (Multiplicative.toAdd a) from rfl, exp_le_exp] at this; simpa using this
    have h2' : ¬ Multiplicative.toAdd a ≤ -2 := by
      intro hle; apply h2
      rw [show (a : ℤᵐ⁰) = exp (Multiplicative.toAdd a) from rfl, exp_le_exp]; simpa using hle
    rw [show (a : ℤᵐ⁰) = exp (Multiplicative.toAdd a) from rfl]
    congr 1; omega
  -- the local vector
  set x := coordOf S (ϖE : E)
  have hx : x ∈ latE S := by rw [mem_latE, cE_coordOf]; exact ϖE.2
  refine ⟨locVec v x, locVec_mem_loc v hx, ?_⟩
  have hN : Nv v (D := D) (locVec v x) = algebraMap F (v.adicCompletion F)
      (algebraMap (𝓞 F) F (Algebra.intNorm (𝓞 F) (𝓞 E) ϖE)) := by
    rw [Algebra.algebraMap_intNorm (L := E)]
    rw [show algebraMap (𝓞 E) E ϖE = cE S x from (cE_coordOf S _).symm, norm_cE]
    simp only [Nv, dv, dIn, locVec_apply, map_add, map_mul, map_pow]
  rw [hN, valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, hval]

/-! ### The norm index $j(\Gamma)$ -/

variable {S v} (L : LocData S v)

theorem Nv_φ (z : Γ L) : Nv v (D := D) (φ L z) =
    ((QuadraticAlgebra.norm z : v.adicCompletionIntegers F) : v.adicCompletion F) := φ_norm L z

theorem two_mul_φ (z : Γ L) : 2 * φ L z 0 =
    ((QuadraticAlgebra.trace z : v.adicCompletionIntegers F) : v.adicCompletion F) := by
  have hb := b_eq L
  have h2 : ((2 : v.adicCompletionIntegers F) : v.adicCompletion F) = 2 := rfl
  rw [φ_zero', QuadraticAlgebra.trace_def]
  push_cast
  rw [hb, h2]; ring

theorem exists_φ_of_integral {y : Fin 2 → v.adicCompletion F} (hT : Valued.v (2 * y 0) ≤ 1)
    (hN : Valued.v (Nv v (D := D) y) ≤ 1) : ∃ z : Γ L, φ L z = y :=
  (mem_loc_iff_φ L y).mp (mem_loc_of_integral S v hT hN)

theorem coe_unit_ne_zero (u : (v.adicCompletionIntegers F)ˣ) :
    ((u : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 := by
  have := valued_unit_eq_one v u.isUnit
  intro h0; rw [h0, map_zero] at this; exact zero_ne_one this

/-- A unit $u$ which is a value $N(y)$ with $\mathrm{Tr}(y)$ integral is a norm from $\Gamma^\times$. -/
theorem mem_range_normΓ_of {u : (v.adicCompletionIntegers F)ˣ} {y : Fin 2 → v.adicCompletion F}
    (hT : Valued.v (2 * y 0) ≤ 1) (hN : Nv v (D := D) y = ((u : v.adicCompletionIntegers F) : v.adicCompletion F)) :
    u ∈ (normΓ v L.a L.b).range := by
  have hN' : Valued.v (Nv v (D := D) y) ≤ 1 := by
    rw [hN]; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp u.1.2
  obtain ⟨z, hz⟩ := exists_φ_of_integral L hT hN'
  have hnz : QuadraticAlgebra.norm z = (u : v.adicCompletionIntegers F) := by
    apply Subtype.ext; rw [← Nv_φ, hz, hN]
  have hzu : IsUnit z := QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (by rw [hnz]; exact u.isUnit)
  exact ⟨hzu.unit, Units.ext (by rw [Units.coe_map, IsUnit.unit_spec]; exact hnz)⟩

theorem ψv_coe_of_mem_range {u : (v.adicCompletionIntegers F)ˣ} (hu : u ∈ (normΓ v L.a L.b).range) :
    ψv v (D := D) ((u : v.adicCompletionIntegers F) : v.adicCompletion F) = 1 := by
  obtain ⟨z, rfl⟩ := hu
  have : (((normΓ v L.a L.b z : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : v.adicCompletion F) =
      Nv v (D := D) (φ L (z : Γ L)) := by rw [Nv_φ]; rfl
  rw [this]; exact ψv_Nv S v _

/-- **Split: $j(\Gamma) = 1$** (every unit $u$ is $N(y)$ for $y = ((u+1)/2, (u-1)/2r)$, $-d = r^2$; $\mathrm{Tr}(y) = u + 1$). -/
theorem jΓ_split (h : relChar E v = 1) : jΓ v L.a L.b = 1 := by
  obtain ⟨r, hr⟩ := (isSquare_neg_dv_iff S v).mpr h
  have hr0 : r ≠ 0 := by
    rintro rfl; rw [mul_zero, neg_eq_zero] at hr; exact dv_ne_zero S v hr
  rw [jΓ, Subgroup.index_eq_one, MonoidHom.range_eq_top]
  intro u
  set uF := ((u : v.adicCompletionIntegers F) : v.adicCompletion F)
  set y : Fin 2 → v.adicCompletion F := ![(uF + 1) / 2, (uF - 1) / (2 * r)]
  have hT : Valued.v (2 * y 0) ≤ 1 := by
    have : 2 * y 0 = uF + 1 := by simp [y]; field_simp
    rw [this]
    exact Valuation.map_add_le _ ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp u.1.2) (by simp)
  have hN : Nv v (D := D) y = uF := by
    have hd : dv v (D := D) = -(r * r) := by rw [← hr, neg_neg]
    simp only [Nv, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, hd]
    field_simp; ring
  obtain ⟨w, hw⟩ := mem_range_normΓ_of L hT hN
  exact ⟨w, hw⟩

/-- **Inert: $j(\Gamma) = 1$** ($\psi$ is trivial on units, so every unit is a local norm $N(y)$, and $\mathrm{Tr}(y)$ is integral by Hensel). -/
theorem jΓ_inert (h : relChar E v = -1) : jΓ v L.a L.b = 1 := by
  have hns : ¬ IsSquare (-dv v (D := D)) := by rw [isSquare_neg_dv_iff S v, h]; decide
  rw [jΓ, Subgroup.index_eq_one, MonoidHom.range_eq_top]
  intro u
  obtain ⟨x₀, x₁, hx⟩ := (ψv_eq_one_iff S v _).mp ((ψv_inert S v h).1 _ u.isUnit)
  have hN : Nv v (D := D) ![x₀, x₁] = ((u : v.adicCompletionIntegers F) : v.adicCompletion F) := by
    simp [Nv, hx]
  have hT := two_mul_le_one_of_norm v hns (y := ![x₀, x₁]) (by
    rw [hN]; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp u.1.2)
  obtain ⟨w, hw⟩ := mem_range_normΓ_of L hT hN
  exact ⟨w, hw⟩

include S in
theorem ψv_pow_of_eq_one {n : v.adicCompletion F} (hn0 : n ≠ 0) (hn : ψv v (D := D) n = 1) (m : ℕ) :
    ψv v (D := D) (n ^ m) = 1 := by
  induction m with
  | zero => rw [pow_zero]; exact (ψv_eq_one_iff S v 1).mpr ⟨1, 0, by ring⟩
  | succ m ih => rw [pow_succ, ψv_mul S v (pow_ne_zero _ hn0) hn0, ih, hn, mul_one]

/-- **Ramified: $j(\Gamma) = 2$** ($N(\Gamma^\times) = \ker\psi|_{\mathfrak o^\times}$, and $\psi$ is nontrivial on units because some local norm has
odd valuation). -/
theorem jΓ_ramified (h : relChar E v = 0) : jΓ v L.a L.b = 2 := by
  have hns : ¬ IsSquare (-dv v (D := D)) := by rw [isSquare_neg_dv_iff S v, h]; decide
  -- membership in the norm group = ψ = 1
  have hmem : ∀ u : (v.adicCompletionIntegers F)ˣ, u ∈ (normΓ v L.a L.b).range ↔
      ψv v (D := D) ((u : v.adicCompletionIntegers F) : v.adicCompletion F) = 1 := by
    intro u
    refine ⟨ψv_coe_of_mem_range L, fun hψ => ?_⟩
    obtain ⟨x₀, x₁, hx⟩ := (ψv_eq_one_iff S v _).mp hψ
    have hN : Nv v (D := D) ![x₀, x₁] = ((u : v.adicCompletionIntegers F) : v.adicCompletion F) := by
      simp [Nv, hx]
    have hT := two_mul_le_one_of_norm v hns (y := ![x₀, x₁]) (by
      rw [hN]; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp u.1.2)
    exact mem_range_normΓ_of L hT hN
  -- a unit with ψ = -1
  obtain ⟨x, hx0, hx⟩ := exists_ψv_neg S v hns
  obtain ⟨y, hy, hyv⟩ := exists_mem_loc_valued_Nv_ramified S v h
  set n := Nv v (D := D) y
  have hn0 : n ≠ 0 := by intro h0; rw [h0, map_zero] at hyv; exact exp_ne_zero hyv.symm
  have hnψ : ψv v (D := D) n = 1 := ψv_Nv S v y
  have hninv : ψv v (D := D) n⁻¹ = 1 := by
    have : n⁻¹ = n * (n⁻¹) ^ 2 := by field_simp
    rw [this, ψv_mul S v hn0 (pow_ne_zero 2 (inv_ne_zero hn0)), hnψ, ψv_sq S v, one_mul]
  obtain ⟨k, hk⟩ := exists_valued_eq_exp v hx0
  obtain ⟨w, hw0, hwψ, hwv⟩ : ∃ w : v.adicCompletion F, w ≠ 0 ∧ ψv v (D := D) w = -1 ∧ Valued.v w = 1 := by
    rcases le_or_gt 0 k with hk0 | hk0
    · refine ⟨x * n ^ k.toNat, mul_ne_zero hx0 (pow_ne_zero _ hn0), ?_, ?_⟩
      · rw [ψv_mul S v hx0 (pow_ne_zero _ hn0), hx, ψv_pow_of_eq_one (S := S) hn0 hnψ, mul_one]
      · rw [map_mul, map_pow, hk, hyv, ← WithZero.exp_nsmul, ← exp_add]
        rw [← exp_zero]; congr 1; simp; omega
    · refine ⟨x * (n⁻¹) ^ (-k).toNat, mul_ne_zero hx0 (pow_ne_zero _ (inv_ne_zero hn0)), ?_, ?_⟩
      · rw [ψv_mul S v hx0 (pow_ne_zero _ (inv_ne_zero hn0)), hx,
          ψv_pow_of_eq_one (S := S) (inv_ne_zero hn0) hninv, mul_one]
      · rw [map_mul, map_pow, map_inv₀, hk, hyv, ← WithZero.exp_neg, ← WithZero.exp_nsmul, ← exp_add]
        rw [← exp_zero]; congr 1; simp; omega
  have hwO : Valued.v w ≤ 1 := hwv.le
  set wO : v.adicCompletionIntegers F := toO v w hwO
  have hwu : IsUnit wO := by
    have hinv : Valued.v w⁻¹ ≤ 1 := by rw [map_inv₀, hwv, inv_one]
    refine isUnit_iff_exists_inv.mpr ⟨toO v w⁻¹ hinv, Subtype.ext ?_⟩
    show w * w⁻¹ = 1
    exact mul_inv_cancel₀ hw0
  rw [jΓ, Subgroup.index_eq_two_iff]
  refine ⟨hwu.unit, fun u => ?_⟩
  rw [hmem, hmem]
  have hu0 := coe_unit_ne_zero u
  have hcoe : ((((u * hwu.unit : (v.adicCompletionIntegers F)ˣ)) : v.adicCompletionIntegers F) : v.adicCompletion F) =
      ((u : v.adicCompletionIntegers F) : v.adicCompletion F) * w := by
    rw [Units.val_mul, IsUnit.unit_spec]; rfl
  rw [hcoe, ψv_mul S v hu0 hw0, hwψ]
  rcases ψv_eq_one_or v (D := D) ((u : v.adicCompletionIntegers F) : v.adicCompletion F) with h1 | h1 <;>
    rw [h1] <;> decide

/-! ### The unit count $|\Gamma_1^\times|$ -/

section Basis

variable {K : Type*} [CommRing K] {a' b' : K}

/-- **A basis $\{1, z\}$** of `QuadraticAlgebra K a' b'` when $z_1$ is a unit: $(\beta, \gamma) \mapsto \beta + \gamma z$. -/
def basisEquiv (z : QuadraticAlgebra K a' b') (hz : IsUnit z.im) : K × K ≃ QuadraticAlgebra K a' b' where
  toFun p := ⟨p.1 + p.2 * z.re, p.2 * z.im⟩
  invFun w := (w.re - w.im * (hz.unit⁻¹ : Kˣ) * z.re, w.im * (hz.unit⁻¹ : Kˣ))
  left_inv p := by
    have h1 : z.im * ((hz.unit⁻¹ : Kˣ) : K) = 1 := IsUnit.mul_val_inv hz
    ext
    · simp only; linear_combination (-(p.2 * z.re)) * h1
    · simp only; linear_combination p.2 * h1
  right_inv w := by
    have h1 : z.im * ((hz.unit⁻¹ : Kˣ) : K) = 1 := IsUnit.mul_val_inv hz
    refine QuadraticAlgebra.ext ?_ ?_ <;> simp only
    · ring
    · linear_combination w.im * h1

theorem norm_basisEquiv (z : QuadraticAlgebra K a' b') (hz : IsUnit z.im) (p : K × K) :
    QuadraticAlgebra.norm (basisEquiv z hz p) =
      p.1 ^ 2 + p.1 * p.2 * QuadraticAlgebra.trace z + p.2 ^ 2 * QuadraticAlgebra.norm z := by
  simp only [basisEquiv, Equiv.coe_fn_mk, QuadraticAlgebra.norm_def, QuadraticAlgebra.trace_def]
  ring

end Basis

instance isMaximal_span_π_one : (Ideal.span {πv v ^ 1}).IsMaximal := by
  rw [pow_one]; exact PrincipalIdealRing.isMaximal_of_irreducible (NF.irreducible_π v)

theorem card_ne_zero_Ok1 : Nat.card {x : Ok v 1 // x ≠ 0} = qv v - 1 := by
  classical
  have h3 : Nat.card {y : Ok v 1 // y = 0} + Nat.card {y : Ok v 1 // ¬ y = 0} = Nat.card (Ok v 1) := by
    rw [← Nat.card_sum]; exact Nat.card_congr (Equiv.sumCompl _)
  have h4 : Nat.card {y : Ok v 1 // y = 0} = 1 := Nat.card_unique
  have h5 : Nat.card (Ok v 1) = qv v := by rw [card_Ok, pow_one]
  show Nat.card {y : Ok v 1 // ¬ y = 0} = _
  omega

theorem mk_one_eq_zero_iff (x : v.adicCompletionIntegers F) :
    Ideal.Quotient.mk (Ideal.span {πv v ^ 1}) x = 0 ↔ Valued.v (x : v.adicCompletion F) < 1 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, ← mem_maximalIdeal_iff_valued v, pow_one,
    (NF.irreducible_π v).maximalIdeal_eq]

/-- **Units of $\Gamma_1$ when a non-constant $\bar z$ is known:** $|\Gamma_1^\times| = \#\{(\beta,\gamma) : \beta^2 + \beta\gamma\bar t + \gamma^2\bar n \ne 0\}$. -/
theorem card_units_QAk1_eq (z : QAk v L.a L.b 1) (hz : z.im ≠ 0) :
    Nat.card (QAk v L.a L.b 1)ˣ = Nat.card {p : Ok v 1 × Ok v 1 //
      p.1 ^ 2 + p.1 * p.2 * QuadraticAlgebra.trace z + p.2 ^ 2 * QuadraticAlgebra.norm z ≠ 0} := by
  have hzu : IsUnit z.im := (isUnit_one_iff v _).mpr hz
  rw [card_units_eq_card_isUnit]
  refine (Nat.card_congr (Equiv.subtypeEquiv (basisEquiv z hzu) fun p => ?_)).symm
  rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, norm_basisEquiv, isUnit_one_iff]

theorem redΓ_trace (z : Γ L) : QuadraticAlgebra.trace (redΓ v L.a L.b 1 z) =
    Ideal.Quotient.mk _ (QuadraticAlgebra.trace z) := QuadraticAlgebra.trace_mapRingHom _ _ _ z

theorem redΓ_norm (z : Γ L) : QuadraticAlgebra.norm (redΓ v L.a L.b 1 z) =
    Ideal.Quotient.mk _ (QuadraticAlgebra.norm z) := QuadraticAlgebra.norm_mapRingHom _ _ _ z

/-- **Split: $|\Gamma_1^\times| = (q-1)^2$** (an idempotent $e \in \Gamma$, $\mathrm{Tr}(e) = 1$, $N(e) = 0$, from maximality; $N(\beta + \gamma\bar e) =
\beta(\beta + \gamma)$). -/
theorem card_units_split (h : relChar E v = 1) :
    Nat.card (QAk v L.a L.b 1)ˣ = (qv v - 1) * (qv v - 1) := by
  obtain ⟨r, hr⟩ := (isSquare_neg_dv_iff S v).mpr h
  have hr0 : r ≠ 0 := by
    rintro rfl; rw [mul_zero, neg_eq_zero] at hr; exact dv_ne_zero S v hr
  set y : Fin 2 → v.adicCompletion F := ![1 / 2, -1 / (2 * r)]
  have hT : Valued.v (2 * y 0) ≤ 1 := by
    have : 2 * y 0 = 1 := by simp [y]
    rw [this, map_one]
  have hN0 : Nv v (D := D) y = 0 := by
    have hd : dv v (D := D) = -(r * r) := by rw [← hr, neg_neg]
    simp only [Nv, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, hd]
    field_simp; ring
  obtain ⟨ze, hze⟩ := exists_φ_of_integral L hT (by rw [hN0, map_zero]; exact zero_le)
  have hnz : QuadraticAlgebra.norm ze = 0 := by
    apply Subtype.ext; rw [← Nv_φ, hze, hN0]; rfl
  have htz : QuadraticAlgebra.trace ze = 1 := by
    apply Subtype.ext; rw [← two_mul_φ, hze]; simp [y]
  set e := redΓ v L.a L.b 1 ze
  have hne : QuadraticAlgebra.norm e = 0 := by rw [redΓ_norm, hnz, map_zero]
  have hte : QuadraticAlgebra.trace e = 1 := by rw [redΓ_trace, htz, map_one]
  have hei : e.im ≠ 0 := by
    intro h0
    have hn := hne
    rw [QuadraticAlgebra.norm_def, h0] at hn
    simp only [mul_zero, sub_zero, add_zero] at hn
    have hre : e.re = 0 := by
      by_contra hre'
      exact ((isUnit_one_iff v _).mpr hre').ne_zero (by rw [← sq] at hn; exact pow_eq_zero_iff (n := 2) two_ne_zero |>.mp hn)
    rw [QuadraticAlgebra.trace_def, hre, h0, mul_zero, mul_zero, add_zero] at hte
    haveI : Fact (1 ≤ 1) := ⟨le_rfl⟩
    exact zero_ne_one hte
  rw [card_units_QAk1_eq L e hei, hte, hne]
  have e2 : {p : Ok v 1 × Ok v 1 // p.1 ^ 2 + p.1 * p.2 * 1 + p.2 ^ 2 * 0 ≠ 0} ≃
      {x : Ok v 1 // x ≠ 0} × {x : Ok v 1 // x ≠ 0} :=
    { toFun := fun p => (⟨p.1.1, fun h0 => p.2 (by rw [h0]; ring)⟩,
        ⟨p.1.1 + p.1.2, fun h0 => p.2 (by linear_combination p.1.1 * h0)⟩)
      invFun := fun q => ⟨(q.1.1, q.2.1 - q.1.1), by
        have := ((isUnit_one_iff v _).mpr q.1.2).mul ((isUnit_one_iff v _).mpr q.2.2)
        intro h0; apply this.ne_zero; linear_combination h0⟩
      left_inv := fun p => by apply Subtype.ext; ext <;> simp
      right_inv := fun q => by ext <;> simp }
  rw [Nat.card_congr e2, Nat.card_prod, card_ne_zero_Ok1]

theorem valued_le_exp_neg_one_of_lt {x : v.adicCompletionIntegers F} (hx : Valued.v (x : v.adicCompletion F) < 1) :
    Valued.v (x : v.adicCompletion F) ≤ exp (-1 : ℤ) := by
  have := (mem_maximalIdeal_iff_valued v x).mpr hx
  rw [(NF.irreducible_π v).maximalIdeal_eq, ← pow_one (NF.π v), NF.mem_span_π_pow] at this
  simpa using this

theorem not_valued_sq_eq_exp_neg_one (w : v.adicCompletion F) : Valued.v (w ^ 2) ≠ exp (-1 : ℤ) := by
  intro h
  by_cases hw : w = 0
  · rw [hw, zero_pow two_ne_zero, map_zero] at h; exact exp_ne_zero h.symm
  obtain ⟨m, hm⟩ := exists_valued_eq_exp v hw
  rw [map_pow, hm, ← WithZero.exp_nsmul, exp_inj] at h
  simp at h; omega

include S in
/-- In the non-split case $N(y) = 0 \Rightarrow y = 0$ (the norm form is anisotropic). -/
theorem eq_zero_of_Nv_eq_zero (hns : ¬ IsSquare (-dv v (D := D))) {y : Fin 2 → v.adicCompletion F}
    (hN : Nv v (D := D) y = 0) : y = 0 := by
  by_cases hy1 : y 1 = 0
  · have : y 0 ^ 2 = 0 := by simpa [Nv, hy1] using hN
    exact vec2_ext (by simpa using pow_eq_zero_iff (n := 2) two_ne_zero |>.mp this) hy1
  · exfalso; apply hns
    refine ⟨y 0 / y 1, ?_⟩
    field_simp
    linear_combination -hN

/-- **Ramified: $|\Gamma_1^\times| = q(q-1)$** (an element $\Pi$ with $v(N\Pi) = 1$ has $\mathrm{Tr}(\Pi) \in \mathfrak p$ by Hensel, so
$N(\beta + \gamma\bar\Pi) = \beta^2$). -/
theorem card_units_ramified (h : relChar E v = 0) :
    Nat.card (QAk v L.a L.b 1)ˣ = qv v * (qv v - 1) := by
  have hns : ¬ IsSquare (-dv v (D := D)) := by rw [isSquare_neg_dv_iff S v, h]; decide
  obtain ⟨y, hy, hyv⟩ := exists_mem_loc_valued_Nv_ramified S v h
  obtain ⟨z, rfl⟩ := (mem_loc_iff_φ L y).mp hy
  set N := QuadraticAlgebra.norm z
  set t := QuadraticAlgebra.trace z
  have hNv : Valued.v (N : v.adicCompletion F) = exp (-1 : ℤ) := by rw [← Nv_φ]; exact hyv
  have hNm : N ∈ maximalIdeal (v.adicCompletionIntegers F) :=
    (mem_maximalIdeal_iff_valued v N).mpr (by rw [hNv, ← exp_zero, exp_lt_exp]; omega)
  have ht0 : Ideal.Quotient.mk (Ideal.span {πv v ^ 1}) t = 0 := by
    by_contra hne
    have htu : IsUnit t := by
      have := (isUnit_mk_iff v le_rfl t).mp ((isUnit_one_iff v _).mpr hne)
      exact DVR.dvr_isUnit_of_not_dvd (NF.irreducible_π v) this
    obtain ⟨r, hr⟩ := hensel_quad v htu hNm
    have hr' : (r : v.adicCompletion F) ^ 2 - (t : v.adicCompletion F) * r + N = 0 := by
      have := congrArg Subtype.val hr; push_cast at this; exact this
    have htF : (t : v.adicCompletion F) = 2 * φ L z 0 := (two_mul_φ L z).symm
    have hNF : (N : v.adicCompletion F) = Nv v (D := D) (φ L z) := (Nv_φ L z).symm
    by_cases hy1 : φ L z 1 = 0
    · apply not_valued_sq_eq_exp_neg_one (φ L z 0)
      rw [← hyv]; simp [Nv, hy1]
    · apply hns
      refine ⟨(2 * r - t) / (2 * φ L z 1), ?_⟩
      have h2 : (2 : v.adicCompletion F) ≠ 0 := two_ne_zero
      field_simp
      rw [htF] at hr' ⊢; rw [hNF] at hr'
      simp only [Nv] at hr'
      linear_combination -4 * hr'
  set e := redΓ v L.a L.b 1 z
  have hne : QuadraticAlgebra.norm e = 0 := by
    rw [redΓ_norm, mk_one_eq_zero_iff, hNv, ← exp_zero, exp_lt_exp]; omega
  have hte : QuadraticAlgebra.trace e = 0 := by rw [redΓ_trace]; exact ht0
  have hei : e.im ≠ 0 := by
    intro h0
    have hn := hne
    rw [QuadraticAlgebra.norm_def, h0] at hn
    simp only [mul_zero, sub_zero, add_zero] at hn
    have hre : e.re = 0 := by
      by_contra hre'
      exact ((isUnit_one_iff v _).mpr hre').ne_zero (by rw [← sq] at hn; exact pow_eq_zero_iff (n := 2) two_ne_zero |>.mp hn)
    have h1 := valued_le_exp_neg_one_of_lt ((mk_one_eq_zero_iff z.re).mp hre)
    have h2 := valued_le_exp_neg_one_of_lt ((mk_one_eq_zero_iff z.im).mp h0)
    apply not_lt.mpr (le_of_eq hNv.symm)
    rw [show (N : v.adicCompletion F) = (z.re : v.adicCompletion F) * z.re + (L.b : v.adicCompletion F) * z.re * z.im -
        (L.a : v.adicCompletion F) * z.im * z.im by simp only [N, QuadraticAlgebra.norm_def]; push_cast; ring]
    have hab : Valued.v (L.a : v.adicCompletion F) ≤ 1 ∧ Valued.v (L.b : v.adicCompletion F) ≤ 1 :=
      ⟨(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp L.a.2,
        (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp L.b.2⟩
    have hle : ∀ x y : v.adicCompletion F, Valued.v x ≤ exp (-1 : ℤ) → Valued.v y ≤ exp (-1 : ℤ) →
        Valued.v (x * y) ≤ exp (-2 : ℤ) := fun x y hx hy => by
      rw [map_mul]
      calc Valued.v x * Valued.v y ≤ exp (-1 : ℤ) * exp (-1 : ℤ) := mul_le_mul' hx hy
        _ = exp (-2 : ℤ) := by rw [← exp_add]; norm_num
    calc Valued.v ((z.re : v.adicCompletion F) * z.re + (L.b : v.adicCompletion F) * z.re * z.im -
          (L.a : v.adicCompletion F) * z.im * z.im)
        ≤ exp (-2 : ℤ) := by
          refine Valuation.map_sub_le _ (Valuation.map_add_le _ (hle _ _ h1 h1) ?_) ?_
          · rw [mul_assoc, map_mul]
            exact (mul_le_of_le_one_left' hab.2).trans (hle _ _ h1 h2)
          · rw [mul_assoc, map_mul]
            exact (mul_le_of_le_one_left' hab.1).trans (hle _ _ h2 h2)
      _ < exp (-1 : ℤ) := by rw [exp_lt_exp]; norm_num
  rw [card_units_QAk1_eq L e hei, hte, hne]
  have e2 : {p : Ok v 1 × Ok v 1 // p.1 ^ 2 + p.1 * p.2 * 0 + p.2 ^ 2 * 0 ≠ 0} ≃ {x : Ok v 1 // x ≠ 0} × Ok v 1 :=
    { toFun := fun p => (⟨p.1.1, fun h0 => p.2 (by rw [h0]; ring)⟩, p.1.2)
      invFun := fun q => ⟨(q.1.1, q.2), by
        have := ((isUnit_one_iff v _).mpr q.1.2).pow 2
        intro h0; apply this.ne_zero; linear_combination h0⟩
      left_inv := fun p => rfl
      right_inv := fun q => rfl }
  rw [Nat.card_congr e2, Nat.card_prod, card_ne_zero_Ok1, card_Ok, pow_one, mul_comm]

theorem φ_smul_π (z : Γ L) :
    φ L ⟨πv v * z.re, πv v * z.im⟩ = πF v • φ L z := by
  apply vec2_ext
  · show φ L ⟨πv v * z.re, πv v * z.im⟩ 0 = πF v * φ L z 0
    rw [φ_zero', φ_zero']; push_cast; ring
  · show φ L ⟨πv v * z.re, πv v * z.im⟩ 1 = πF v * φ L z 1
    rw [φ_one', φ_one']; push_cast; ring

include S in
theorem ψv_πF_pow (h : relChar E v = -1) (m : ℕ) : ψv v (D := D) (πF v ^ m) = (-1) ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero]; exact (ψv_eq_one_iff S v 1).mpr ⟨1, 0, by ring⟩
  | succ m ih =>
    rw [pow_succ, ψv_mul S v (pow_ne_zero _ (πF_ne_zero v)) (πF_ne_zero v), ih, (ψv_inert S v h).2, pow_succ]

/-- **Inert: $|\Gamma_1^\times| = q^2 - 1$** ($\Gamma_1$ is a field: a norm in $\mathfrak p$ has even valuation, hence lies in $\mathfrak p^2$, and then
$z/\varpi \in \Gamma$ by Hensel and maximality). -/
theorem card_units_inert (h : relChar E v = -1) :
    Nat.card (QAk v L.a L.b 1)ˣ = qv v ^ 2 - 1 := by
  have hns : ¬ IsSquare (-dv v (D := D)) := by rw [isSquare_neg_dv_iff S v, h]; decide
  have hunit : ∀ w : QAk v L.a L.b 1, w ≠ 0 → IsUnit w := by
    intro w hw
    by_contra hwu
    obtain ⟨z, rfl⟩ := redΓ_surjective v L.a L.b 1 w
    have hn0 : Ideal.Quotient.mk (Ideal.span {πv v ^ 1}) (QuadraticAlgebra.norm z) = 0 := by
      by_contra hne
      apply hwu
      rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, redΓ_norm]
      exact (isUnit_one_iff v _).mpr hne
    set n := ((QuadraticAlgebra.norm z : v.adicCompletionIntegers F) : v.adicCompletion F)
    have hnlt : Valued.v n < 1 := (mk_one_eq_zero_iff (QuadraticAlgebra.norm z)).mp hn0
    by_cases hnz : n = 0
    · apply hw
      have hφ : φ L z = 0 := eq_zero_of_Nv_eq_zero (S := S) hns (by rw [Nv_φ]; exact hnz)
      have hz : z = 0 := φ_injective L (by
        rw [hφ]; apply vec2_ext <;> simp [φ_zero', φ_one'])
      rw [hz, map_zero]
    obtain ⟨m, hm⟩ := exists_valued_eq_exp v hnz
    have hm1 : m ≤ -1 := by
      rw [hm, ← exp_zero, exp_lt_exp] at hnlt; omega
    -- ψ(n) = 1 forces m even
    set k := (-m).toNat
    have hk : (m : ℤ) = -(k : ℤ) := by omega
    obtain ⟨u, hu_def⟩ : ∃ u : v.adicCompletion F, u = n * (πF v)⁻¹ ^ k := ⟨_, rfl⟩
    have hu1 : Valued.v u = 1 := by
      rw [hu_def, map_mul, map_pow, map_inv₀, valued_πF, hm, hk, ← WithZero.exp_neg, ← WithZero.exp_nsmul, ← exp_add]
      rw [← exp_zero]; congr 1; simp
    have huO : Valued.v u ≤ 1 := hu1.le
    have huU : IsUnit (toO v u huO) := by
      have hinv : Valued.v u⁻¹ ≤ 1 := by rw [map_inv₀, hu1, inv_one]
      have hu0 : u ≠ 0 := by intro h0; rw [h0, map_zero] at hu1; exact zero_ne_one hu1
      exact isUnit_iff_exists_inv.mpr ⟨toO v u⁻¹ hinv, Subtype.ext (mul_inv_cancel₀ hu0)⟩
    have hψu : ψv v (D := D) u = 1 := (ψv_inert S v h).1 (toO v u huO) huU
    have hnu : n = πF v ^ k * u := by
      rw [hu_def, inv_pow, ← mul_assoc, mul_comm (πF v ^ k), mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (πF_ne_zero v)),
        mul_one]
    have hnN : n = Nv v (D := D) (φ L z) := (Nv_φ L z).symm
    have hψn : ψv v (D := D) n = 1 := by rw [hnN]; exact ψv_Nv S v _
    have hu0 : u ≠ 0 := by intro h0; rw [h0, map_zero] at hu1; exact zero_ne_one hu1
    rw [hnu, ψv_mul S v (pow_ne_zero _ (πF_ne_zero v)) hu0, ψv_πF_pow (S := S) h, hψu, mul_one] at hψn
    have hkeven : Even k := by
      by_contra hodd
      rw [Nat.not_even_iff_odd] at hodd
      rw [hodd.neg_one_pow] at hψn
      exact absurd hψn (by decide)
    have hk2 : 2 ≤ k := by
      obtain ⟨j, hj⟩ := hkeven; omega
    -- y' = φ z / π is in Λ
    set y' : Fin 2 → v.adicCompletion F := (πF v)⁻¹ • φ L z
    have hNy' : Nv v (D := D) y' = n * ((πF v)⁻¹) ^ 2 := by
      rw [hnN]; simp only [Nv, y', Pi.smul_apply, smul_eq_mul]; ring
    have hNy'1 : Valued.v (Nv v (D := D) y') ≤ 1 := by
      rw [hNy', map_mul, map_pow, map_inv₀, valued_πF, hm, hk, ← WithZero.exp_neg, ← WithZero.exp_nsmul, ← exp_add,
        ← exp_zero, exp_le_exp]
      simp; omega
    have hTy' := two_mul_le_one_of_norm v hns hNy'1
    obtain ⟨z', hz'⟩ := exists_φ_of_integral L hTy' hNy'1
    have hzz : z = ⟨πv v * z'.re, πv v * z'.im⟩ := by
      apply φ_injective L
      rw [φ_smul_π, hz']
      simp only [y', smul_smul, mul_inv_cancel₀ (πF_ne_zero v), one_smul]
    apply hw
    rw [hzz]
    refine QuadraticAlgebra.ext ?_ ?_
    · show Ideal.Quotient.mk _ (πv v * z'.re) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · show Ideal.Quotient.mk _ (πv v * z'.im) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  rw [card_units_eq_card_isUnit]
  have e : {w : QAk v L.a L.b 1 // IsUnit w} ≃ {w : QAk v L.a L.b 1 // w ≠ 0} :=
    Equiv.subtypeEquivRight fun w => ⟨fun hw h0 => by
      haveI : Fact (1 ≤ 1) := ⟨le_rfl⟩
      rw [h0] at hw; exact not_isUnit_zero hw, hunit w⟩
  rw [Nat.card_congr e]
  classical
  have h3 : Nat.card {y : QAk v L.a L.b 1 // y = 0} + Nat.card {y : QAk v L.a L.b 1 // ¬ y = 0} =
      Nat.card (QAk v L.a L.b 1) := by
    rw [← Nat.card_sum]; exact Nat.card_congr (Equiv.sumCompl _)
  have h4 : Nat.card {y : QAk v L.a L.b 1 // y = 0} = 1 := Nat.card_unique
  have h5 : Nat.card (QAk v L.a L.b 1) = qv v ^ 2 := by rw [card_QAk]
  show Nat.card {y : QAk v L.a L.b 1 // ¬ y = 0} = _
  omega

/-- **The local factor of the maximal order at $\mathfrak p$:**
$$\frac{|\Gamma_1^\times|\,j(\Gamma)}{q(q-1)} = \begin{cases} 2 & \mathfrak p \text{ ramified},\\ 1 - \chi_{E/F}(\mathfrak p)/N\mathfrak p & \text{otherwise}\end{cases}$$
(split: $(q-1)^2/(q(q-1))$; inert: $(q^2-1)/(q(q-1))$; ramified: $2q(q-1)/(q(q-1))$; every prime, dyadic included). -/
theorem localFactor_maximal :
    (Nat.card (QAk v L.a L.b 1)ˣ * jΓ v L.a L.b : ℝ) / (qv v * (qv v - 1)) =
      if relChar E v = 0 then 2 else 1 - (relChar E v : ℝ) / qv v := by
  have hq : (1 : ℝ) < qv v := by exact_mod_cast one_lt_qv v
  have hq1 : ((qv v - 1 : ℕ) : ℝ) = (qv v : ℝ) - 1 := by rw [Nat.cast_sub (one_lt_qv v).le, Nat.cast_one]
  have hq0 : (qv v : ℝ) * ((qv v : ℝ) - 1) ≠ 0 := by nlinarith
  obtain ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ := splitting (Algebra.IsQuadraticExtension.finrank_eq_two F E) v
  · rw [card_units_split L h1, jΓ_split L h1, if_neg (by rw [h1]; decide), h1]
    push_cast; rw [hq1]; field_simp
  · rw [card_units_inert L h1, jΓ_inert L h1, if_neg (by rw [h1]; decide), h1]
    have : ((qv v ^ 2 - 1 : ℕ) : ℝ) = (qv v : ℝ) ^ 2 - 1 := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ (qv_pos v)), Nat.cast_pow, Nat.cast_one]
    push_cast; rw [this]; field_simp; ring
  · rw [card_units_ramified L h1, jΓ_ramified L h1, if_pos h1]
    push_cast; rw [hq1]; field_simp

end QuadFormsKB.Tamagawa.BinaryCM
