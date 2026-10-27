/-
# O'Meara §81D: existence of the invariant factors (Theorem 81:11, first part)

**Setting** (as in `Sec81.lean`): $R$ a Dedekind domain with fraction field $F$, $V$ a vector space over $F$,
lattices are finitely generated $R$-submodules, fractional ideals are non-zero finitely generated $R$-submodules of
$F$, $\mathfrak a_x$ = `coeff F L x`.

**Index convention.** O'Meara's base $x_1, \dots, x_n$ and $\mathfrak t_1 \supseteq \cdots \supseteq \mathfrak t_n$ are
`x 0, …, x (n-1)` and `t 0, …, t (n-1)`; "$\mathfrak t_1 \supseteq \mathfrak t_2 \supseteq \cdots$" is `Antitone t`.

**Proves** (O'Meara 1963, §81D, pp. 214–216):
* `exists_smul_mul_sup_eq_one`: for a fractional ideal $\mathfrak X$ and a non-zero integral ideal $\mathfrak N$ there
  is $\gamma \in F^\times$ with $\gamma\mathfrak X$ integral and $\gamma\mathfrak X + \mathfrak N = \mathfrak o$ (the
  ideal-theoretic input of step 3, O'Meara's Example 22:9);
* `exists_invariant_factors_of_le` (Theorem 81:11, existence, for lattices $K \subseteq L$ spanning the same space)
  and `exists_invariant_factors` (**Theorem 81:11**, existence, as stated: lattices $L$, $K$ on $V$).
-/
import QuadFormsKB.Literature.OMeara.Sec81Adapted
import QuadFormsKB.Literature.OMeara.Sec81Change

open Submodule Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]

/-- Coprime scaling inside `FractionalIdeal`, with a non-zero scalar. -/
theorem exists_spanSingleton_mul_add_coeIdeal {J : FractionalIdeal (nonZeroDivisors R) F} (hJ : J ≠ 0)
    {A : Ideal R} (hA : A ≠ ⊥) :
    ∃ γ : F, γ ≠ 0 ∧
      FractionalIdeal.spanSingleton (nonZeroDivisors R) γ * J + (A : FractionalIdeal (nonZeroDivisors R) F) = 1 := by
  obtain ⟨d, B, hd, hJB⟩ := FractionalIdeal.exists_eq_spanSingleton_mul J⁻¹
  have hd' : algebraMap R F d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hd
  have hB : B ≠ ⊥ := by
    rintro rfl
    apply inv_ne_zero hJ; rw [hJB, FractionalIdeal.coeIdeal_bot, mul_zero]
  have hB0 : (B : FractionalIdeal (nonZeroDivisors R) F) ≠ 0 := by rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
  obtain ⟨g, hg⟩ := IsDedekindDomain.exists_sup_span_eq (show A * B ≤ B from Ideal.mul_le_right)
    (mul_ne_zero hA hB)
  -- we may assume `g ≠ 0`
  obtain ⟨g, hg0, hg⟩ : ∃ g : R, g ≠ 0 ∧ A * B ⊔ Ideal.span {g} = B := by
    by_cases h0 : g = 0
    · subst h0
      simp only [Ideal.span_singleton_zero, sup_bot_eq] at hg
      obtain ⟨g', hg'B, hg'0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hB
      refine ⟨g', hg'0, le_antisymm (sup_le Ideal.mul_le_right ((Ideal.span_singleton_le_iff_mem _).mpr hg'B)) ?_⟩
      exact hg.ge.trans le_sup_left
    · exact ⟨g, h0, hg⟩
  have hg' : algebraMap R F g ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hg0
  refine ⟨algebraMap R F g * (algebraMap R F d)⁻¹, mul_ne_zero hg' (inv_ne_zero hd'), ?_⟩
  have e2 : J = FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R F d) *
      (B : FractionalIdeal (nonZeroDivisors R) F)⁻¹ := by
    rw [← inv_inv J, hJB, mul_inv, FractionalIdeal.spanSingleton_inv, inv_inv]
  have e3 : FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R F g * (algebraMap R F d)⁻¹) * J =
      FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R F g) *
        (B : FractionalIdeal (nonZeroDivisors R) F)⁻¹ := by
    rw [e2, ← mul_assoc, ← map_mul, mul_assoc, inv_mul_cancel₀ hd', mul_one]
  rw [e3]
  apply mul_right_cancel₀ hB0
  rw [one_mul, add_mul, mul_assoc, inv_mul_cancel₀ hB0, mul_one, ← FractionalIdeal.coeIdeal_mul,
    ← FractionalIdeal.coeIdeal_span_singleton, add_comm, ← FractionalIdeal.coeIdeal_sup, hg]

/-- **Coprime scaling of a fractional ideal** (the ideal theory behind O'Meara's Example 22:9, used in step 3 of the
proof of 81:11): for a fractional ideal $\mathfrak X$ and a non-zero integral ideal $\mathfrak N$ there is
$\gamma \in F^\times$ with $\gamma\mathfrak X \subseteq \mathfrak o$ and $\gamma\mathfrak X + \mathfrak N = \mathfrak o$. -/
theorem exists_smul_mul_sup_eq_one {X : Submodule R F} (hX : X.FG) (hX0 : X ≠ ⊥) {N : Submodule R F}
    (hN : N ≤ 1) (hN0 : N ≠ ⊥) :
    ∃ γ : F, γ ≠ 0 ∧ span R {γ} * X ≤ 1 ∧ span R {γ} * X ⊔ N = 1 := by
  let I : FractionalIdeal (nonZeroDivisors R) F := ⟨X, FractionalIdeal.isFractional_of_fg hX⟩
  let J : FractionalIdeal (nonZeroDivisors R) F := ⟨N, FractionalIdeal.isFractional_of_le_one N hN⟩
  have hI : I ≠ 0 := by
    intro h0; apply hX0
    have := congrArg (fun J : FractionalIdeal (nonZeroDivisors R) F => (J : Submodule R F)) h0
    simpa [I] using this
  have hJ1 : J ≤ 1 := by
    rw [← FractionalIdeal.coe_le_coe, FractionalIdeal.coe_one]; exact hN
  obtain ⟨A, hAJ⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hJ1
  have hA : A ≠ ⊥ := by
    rintro rfl
    apply hN0
    have := congrArg (fun J : FractionalIdeal (nonZeroDivisors R) F => (J : Submodule R F)) hAJ
    simpa [J] using this.symm
  obtain ⟨γ, hγ, h⟩ := exists_spanSingleton_mul_add_coeIdeal hI hA
  rw [hAJ] at h
  have h2 := congrArg (fun J : FractionalIdeal (nonZeroDivisors R) F => (J : Submodule R F)) h
  simp only [FractionalIdeal.coe_add, FractionalIdeal.coe_mul, FractionalIdeal.coe_spanSingleton,
    FractionalIdeal.coe_one] at h2
  refine ⟨γ, hγ, ?_, ?_⟩
  · rw [← h2]; exact le_sup_left
  · rw [← h2]; rfl

/-- The unit ideal is a fractional ideal. -/
theorem fi_one : (1 : Submodule R F).FG ∧ (1 : Submodule R F) ≠ ⊥ := by
  refine ⟨by rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _, ?_⟩
  intro h
  have : (1 : F) ∈ (1 : Submodule R F) := Submodule.mem_one.mpr ⟨1, map_one _⟩
  rw [h] at this; simp at this

/-- A product of fractional ideals is a fractional ideal. -/
theorem fi_mul {a b : Submodule R F} (ha : a.FG ∧ a ≠ ⊥) (hb : b.FG ∧ b ≠ ⊥) :
    (a * b).FG ∧ a * b ≠ ⊥ := by
  refine ⟨ha.1.mul hb.1, ?_⟩
  rw [← Submodule.zero_eq_bot] at *
  exact mul_ne_zero ha.2 hb.2

/-- A join of fractional ideals is a fractional ideal. -/
theorem fi_sup {a b : Submodule R F} (ha : a.FG ∧ a ≠ ⊥) (hb : b.FG ∧ b ≠ ⊥) :
    (a ⊔ b).FG ∧ a ⊔ b ≠ ⊥ :=
  ⟨ha.1.sup hb.1, fun h => ha.2 (eq_bot_iff.mpr (h ▸ le_sup_left))⟩

/-- The inverse of a fractional ideal is a fractional ideal. -/
theorem fi_one_div {a : Submodule R F} (ha : a.FG ∧ a ≠ ⊥) : (1 / a).FG ∧ 1 / a ≠ ⊥ :=
  one_div_fg ha.1 ha.2

/-- `a * (1 / a) = 1` for a fractional ideal `a`. -/
theorem fi_mul_one_div {a : Submodule R F} (ha : a.FG ∧ a ≠ ⊥) : a * (1 / a) = 1 :=
  mul_one_div_cancel_of_fg ha.1 ha.2

/-- Cancellation of a fractional ideal. -/
theorem fi_mul_right_cancel {a b c : Submodule R F} (hc : c.FG ∧ c ≠ ⊥) (h : a * c = b * c) : a = b :=
  calc a = a * (c * (1 / c)) := by rw [fi_mul_one_div hc, mul_one]
    _ = (a * c) * (1 / c) := by ring
    _ = (b * c) * (1 / c) := by rw [h]
    _ = b * (c * (1 / c)) := by ring
    _ = b := by rw [fi_mul_one_div hc, mul_one]

/-- Inversion reverses inclusion of fractional ideals. -/
theorem fi_one_div_le {a b : Submodule R F} (ha : a.FG ∧ a ≠ ⊥) (hb : b.FG ∧ b ≠ ⊥) (h : a ≤ b) :
    1 / b ≤ 1 / a :=
  calc 1 / b = (1 / b) * (a * (1 / a)) := by rw [fi_mul_one_div ha, mul_one]
    _ = a * (1 / b) * (1 / a) := by ring
    _ ≤ b * (1 / b) * (1 / a) := mul_le_mul' (mul_le_mul' h le_rfl) le_rfl
    _ = 1 / a := by rw [fi_mul_one_div hb, one_mul]

/-- Multiplication by a fractional ideal is strictly monotone. -/
theorem fi_mul_lt_mul {a b c : Submodule R F} (hc : c.FG ∧ c ≠ ⊥) (h : a < b) : a * c < b * c :=
  lt_of_le_of_ne (mul_le_mul' h.le le_rfl) fun he => h.ne (fi_mul_right_cancel hc he)

/-- Double inversion of a fractional ideal. -/
theorem fi_one_div_one_div {a : Submodule R F} (ha : a.FG ∧ a ≠ ⊥) : 1 / (1 / a) = a :=
  fi_mul_right_cancel (fi_one_div ha) <| by
    rw [mul_comm, fi_mul_one_div (fi_one_div ha), fi_mul_one_div ha]

/-- Multiplying by an integral ideal shrinks. -/
theorem mul_le_of_le_one {x y : Submodule R F} (h : x ≤ 1) : x * y ≤ y :=
  calc x * y ≤ 1 * y := mul_le_mul' h le_rfl
    _ = y := one_mul _

/-- If `P * X = 1` and `α X ⊆ 𝔬` then `α ∈ P`. -/
theorem mem_of_mul_eq_one_of_le {P X : Submodule R F} (hPX : P * X = 1) {α : F}
    (h : span R {α} * X ≤ 1) : α ∈ P := by
  have : span R {α} ≤ P :=
    calc span R {α} = span R {α} * (P * X) := by rw [hPX, mul_one]
      _ = P * (span R {α} * X) := by ring
      _ ≤ P * 1 := mul_le_mul' le_rfl h
      _ = P := mul_one _
  exact this (Submodule.mem_span_singleton_self α)

/-- **Coprime pair** (the ideal theory of step 4 of the proof of 81:11). -/
theorem exists_coprime_pair {A₁ A₂ T₁ T₂ : Submodule R F} (hA₁ : A₁.FG ∧ A₁ ≠ ⊥) (hA₂ : A₂.FG ∧ A₂ ≠ ⊥)
    (hT₁ : T₁.FG ∧ T₁ ≠ ⊥) (hT₂ : T₂.FG ∧ T₂ ≠ ⊥) :
    ∃ α β : F, α ≠ 0 ∧ α ∈ A₁ * T₁ ∧ β ∈ A₂ * T₂ ∧
      ∀ γ : F, γ * α ∈ A₁ → γ * β ∈ A₂ → γ ∈ 1 / (T₁ ⊔ T₂) := by
  set S := T₁ ⊔ T₂ with hS
  have hSfi := fi_sup hT₁ hT₂
  have hSinv := fi_mul_one_div hSfi
  set P₁ := T₁ * (1 / S) with hP₁
  set P₂ := T₂ * (1 / S) with hP₂
  have hP₁fi : P₁.FG ∧ P₁ ≠ ⊥ := fi_mul hT₁ (fi_one_div hSfi)
  have hP₂fi : P₂.FG ∧ P₂ ≠ ⊥ := fi_mul hT₂ (fi_one_div hSfi)
  have hP₁le : P₁ ≤ 1 := by
    rw [← hSinv]; exact mul_le_mul' le_sup_left le_rfl
  have hP₂le : P₂ ≤ 1 := by
    rw [← hSinv]; exact mul_le_mul' le_sup_right le_rfl
  have hP12 : P₁ ⊔ P₂ = 1 := by rw [hP₁, hP₂, ← Submodule.sup_mul, hSinv]
  -- first scalar
  set X₁ := (1 / A₁) * (1 / T₁) with hX₁
  have hX₁fi : X₁.FG ∧ X₁ ≠ ⊥ := fi_mul (fi_one_div hA₁) (fi_one_div hT₁)
  obtain ⟨α, hα0, hc1, hc2⟩ := exists_smul_mul_sup_eq_one hX₁fi.1 hX₁fi.2 hP₂le hP₂fi.2
  set c := span R {α} * X₁ with hc
  have hαfi : (span R {α}).FG ∧ span R {α} ≠ ⊥ :=
    ⟨Submodule.fg_span_singleton _, by simpa using hα0⟩
  have hcfi : c.FG ∧ c ≠ ⊥ := fi_mul hαfi hX₁fi
  have hαmem : α ∈ A₁ * T₁ := by
    refine mem_of_mul_eq_one_of_le (X := X₁) ?_ hc1
    calc A₁ * T₁ * X₁ = (A₁ * (1 / A₁)) * (T₁ * (1 / T₁)) := by rw [hX₁]; ring
      _ = 1 := by rw [fi_mul_one_div hA₁, fi_mul_one_div hT₁, mul_one]
  have hcT : c * T₁ = span R {α} * (1 / A₁) :=
    calc c * T₁ = span R {α} * (1 / A₁) * (T₁ * (1 / T₁)) := by rw [hc, hX₁]; ring
      _ = _ := by rw [fi_mul_one_div hT₁, mul_one]
  -- second scalar
  set X₂ := (1 / A₂) * (1 / T₂) with hX₂
  have hX₂fi : X₂.FG ∧ X₂ ≠ ⊥ := fi_mul (fi_one_div hA₂) (fi_one_div hT₂)
  have hcP₁fi : (c * P₁).FG ∧ c * P₁ ≠ ⊥ := fi_mul hcfi hP₁fi
  have hcP₁le : c * P₁ ≤ 1 := by
    calc c * P₁ ≤ 1 * 1 := mul_le_mul' (hc2 ▸ le_sup_left) hP₁le
      _ = 1 := mul_one _
  obtain ⟨β, hβ0, hd1, hd2⟩ := exists_smul_mul_sup_eq_one hX₂fi.1 hX₂fi.2 hcP₁le hcP₁fi.2
  set d := span R {β} * X₂ with hd
  have hβmem : β ∈ A₂ * T₂ := by
    refine mem_of_mul_eq_one_of_le (X := X₂) ?_ hd1
    calc A₂ * T₂ * X₂ = (A₂ * (1 / A₂)) * (T₂ * (1 / T₂)) := by rw [hX₂]; ring
      _ = 1 := by rw [fi_mul_one_div hA₂, fi_mul_one_div hT₂, mul_one]
  have hdT : d * T₂ = span R {β} * (1 / A₂) :=
    calc d * T₂ = span R {β} * (1 / A₂) * (T₂ * (1 / T₂)) := by rw [hd, hX₂]; ring
      _ = _ := by rw [fi_mul_one_div hT₂, mul_one]
  -- coprimality
  have h1 : c * P₁ ⊔ P₂ = 1 := by
    apply le_antisymm (sup_le hcP₁le hP₂le)
    calc (1 : Submodule R F) = (c ⊔ P₂) * (P₁ ⊔ P₂) := by rw [hc2, hP12, mul_one]
      _ = (c * P₁ ⊔ c * P₂) ⊔ (P₂ * P₁ ⊔ P₂ * P₂) := by
          rw [Submodule.sup_mul, Submodule.mul_sup, Submodule.mul_sup]
      _ ≤ c * P₁ ⊔ P₂ := by
          refine sup_le (sup_le le_sup_left ((mul_le_of_le_one hc1).trans le_sup_right))
            (sup_le ?_ ((mul_le_of_le_one hP₂le).trans le_sup_right))
          rw [mul_comm]
          exact (mul_le_of_le_one hP₁le).trans le_sup_right
  have hdle : d ≤ 1 := hd2 ▸ le_sup_left
  have h2 : c * P₁ ⊔ d * P₂ = 1 := by
    apply le_antisymm
    · refine sup_le hcP₁le ?_
      calc d * P₂ ≤ 1 * 1 := mul_le_mul' hdle hP₂le
        _ = 1 := mul_one _
    calc (1 : Submodule R F) = (d ⊔ c * P₁) * (P₂ ⊔ c * P₁) := by rw [hd2, sup_comm P₂, h1, mul_one]
      _ = (d * P₂ ⊔ d * (c * P₁)) ⊔ (c * P₁ * P₂ ⊔ c * P₁ * (c * P₁)) := by
          rw [Submodule.sup_mul, Submodule.mul_sup, Submodule.mul_sup]
      _ ≤ d * P₂ ⊔ c * P₁ := by
          refine sup_le (sup_le le_sup_left ((mul_le_of_le_one hdle).trans le_sup_right))
            (sup_le ?_ ((mul_le_of_le_one hcP₁le).trans le_sup_right))
          rw [mul_comm]
          exact (mul_le_of_le_one hP₂le).trans le_sup_right
      _ = c * P₁ ⊔ d * P₂ := sup_comm _ _
  -- the sum of the two pieces is `S`
  have h3 : span R {α} * (1 / A₁) ⊔ span R {β} * (1 / A₂) = S := by
    apply fi_mul_right_cancel (fi_one_div hSfi)
    have h4 : (c * T₁ ⊔ d * T₂) * (1 / S) = c * P₁ ⊔ d * P₂ := by
      rw [Submodule.sup_mul, mul_assoc c T₁, mul_assoc d T₂]
    rw [← hcT, ← hdT, h4, h2, hS, hSinv]
  refine ⟨α, β, hα0, hαmem, hβmem, fun γ hγα hγβ => ?_⟩
  rw [Submodule.mem_div_iff_forall_mul_mem]
  intro y hy
  rw [← h3] at hy
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨u, hu, rfl⟩ := Submodule.mem_span_singleton_mul.mp hp
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_span_singleton_mul.mp hq
  have e1 : γ * (α * u) ∈ (1 : Submodule R F) := by
    rw [← fi_mul_one_div hA₁, ← mul_assoc]
    exact Submodule.mul_mem_mul hγα hu
  have e2 : γ * (β * w) ∈ (1 : Submodule R F) := by
    rw [← fi_mul_one_div hA₂, ← mul_assoc]
    exact Submodule.mul_mem_mul hγβ hw
  rw [mul_add]
  exact (1 : Submodule R F).add_mem e1 e2

/-- An element of `⨆ i, a i • span {w i}` is a sum `∑ c i • w i` with `c i ∈ a i`. -/
theorem exists_sum_of_mem_iSup {ι : Type*} [Fintype ι] (w : ι → V) (a : ι → Submodule R F) {z : V}
    (hz : z ∈ ⨆ i, a i • span R {w i}) : ∃ c : ι → F, (∀ i, c i ∈ a i) ∧ z = ∑ i, c i • w i := by
  classical
  let N : Submodule R V :=
    { carrier := {z | ∃ c : ι → F, (∀ i, c i ∈ a i) ∧ z = ∑ i, c i • w i}
      add_mem' := by
        rintro _ _ ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
        exact ⟨c + c', fun i => (a i).add_mem (hc i) (hc' i), by simp [add_smul, Finset.sum_add_distrib]⟩
      zero_mem' := ⟨0, fun i => (a i).zero_mem, by simp⟩
      smul_mem' := by
        rintro r _ ⟨c, hc, rfl⟩
        refine ⟨r • c, fun i => (a i).smul_mem r (hc i), ?_⟩
        simp [Finset.smul_sum, smul_assoc] }
  have : (⨆ i, a i • span R {w i}) ≤ N := by
    refine iSup_le fun i => ?_
    rw [Submodule.smul_le]
    intro α hα m hm
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hm
    refine ⟨Pi.single i (r • α), fun j => ?_, ?_⟩
    · by_cases hj : j = i
      · subst hj; simpa using (a j).smul_mem r hα
      · simp [hj]
    · simp [Pi.single_apply, smul_comm α r, smul_assoc]
  exact this hz

/-- Coordinates of a vector of `⨆ i, a i • span {w i}` along an independent family lie in the `a i`. -/
theorem coord_mem_of_mem_iSup {ι : Type*} [Fintype ι] {w : ι → V} (hw : LinearIndependent F w)
    (a : ι → Submodule R F) (c : ι → F) (h : ∑ i, c i • w i ∈ ⨆ i, a i • span R {w i}) :
    ∀ i, c i ∈ a i := by
  classical
  obtain ⟨c', hc', hsum⟩ := exists_sum_of_mem_iSup w a h
  have h0 := Fintype.linearIndependent_iff.mp hw (c - c') (by
    simp [sub_smul, Finset.sum_sub_distrib, hsum])
  have : c = c' := funext fun i => sub_eq_zero.mp (h0 i)
  subst this; exact hc'

/-- A single multiple `β • w k` lies in `⨆ i, a i • span {w i}` iff `β ∈ a k`. -/
theorem smul_mem_iSup_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {w : ι → V} (hw : LinearIndependent F w)
    (a : ι → Submodule R F) (k : ι) (β : F) : β • w k ∈ ⨆ i, a i • span R {w i} ↔ β ∈ a k := by
  constructor
  · intro h
    have := coord_mem_of_mem_iSup hw a (Pi.single k β) (by simpa [Pi.single_apply] using h) k
    simpa using this
  · intro h
    exact Submodule.mem_iSup_of_mem k (Submodule.smul_mem_smul h (Submodule.mem_span_singleton_self _))

/-- The supremum over `Fin (n + 1)` splits off the first index. -/
theorem iSup_cons_aux {n : ℕ} (A : Fin (n + 1) → Submodule R V) :
    ⨆ i, A i = A 0 ⊔ ⨆ i : Fin n, A i.succ := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · exact le_sup_left
    · exact le_sup_of_le_right (le_iSup (fun i : Fin n => A i.succ) j)
  · exact sup_le (le_iSup A _) (iSup_le fun j => le_iSup A _)

/-- `L = (L ∩ F v) ⊕ (L ∩ U)` lets one read off the components of a vector of `L`. -/
theorem mem_and_mem_of_dec {L : Submodule R V} {U : Submodule F V} {v : V} (hvU : v ∉ U)
    (hdec : L = coeff F L v • span R {v} ⊔ (L ⊓ U.restrictScalars R)) {a : F} {u : V} (hu : u ∈ U)
    (h : a • v + u ∈ L) : a • v ∈ L ∧ u ∈ L := by
  rw [hdec] at h
  obtain ⟨m, hm, l, hl, hml⟩ := Submodule.mem_sup.mp h
  rw [coeff_smul_span] at hm
  obtain ⟨hmL, hmv⟩ := hm
  obtain ⟨e, rfl⟩ := Submodule.mem_span_singleton.mp (show m ∈ span F {v} from hmv)
  obtain ⟨hlL, hlU⟩ := hl
  have hlU' : l ∈ U := hlU
  have hae : a = e := by
    by_contra hne
    have h1 : (a - e) • v = l - u := by
      rw [sub_smul]; apply eq_sub_of_add_eq
      rw [sub_add_eq_add_sub, ← hml, add_sub_cancel_left]
    have h2 : (a - e) • v ∈ U := by rw [h1]; exact U.sub_mem hlU' hu
    apply hvU
    have := U.smul_mem (a - e)⁻¹ h2
    rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul] at this
  subst hae
  refine ⟨hmL, ?_⟩
  have : l = u := by simpa using hml
  rw [← this]; exact hlL

/-- A set function into integral ideals has a maximal value (Noetherian). -/
theorem exists_tau_max (s : Set V) (hs : s.Nonempty) (τ : V → Submodule R F) (hτ : ∀ v ∈ s, τ v ≤ 1) :
    ∃ v ∈ s, ∀ v' ∈ s, ¬ τ v < τ v' := by
  set f : R →ₗ[R] F := Algebra.linearMap R F with hf
  have hinj : ∀ A : Submodule R F, A ≤ 1 → Submodule.map f (A.comap f) = A := by
    intro A hA
    rw [Submodule.map_comap_eq, ← Submodule.one_eq_range]
    exact inf_eq_right.mpr hA
  obtain ⟨I, ⟨v, hv, rfl⟩, hmax⟩ := (set_has_maximal_iff_noetherian (R := R) (M := R)).mpr inferInstance
    ((fun v => (τ v).comap f) '' s) (hs.image _)
  refine ⟨v, hv, fun v' hv' hlt => hmax ((τ v').comap f) ⟨v', hv', rfl⟩ ?_⟩
  refine lt_of_le_of_ne (Submodule.comap_mono hlt.le) fun h => hlt.ne ?_
  rw [← hinj _ (hτ v hv), ← hinj _ (hτ v' hv')]
  exact congrArg (Submodule.map f) h

/-- A vector `v ≠ 0` of an `(n+1)`-dimensional space `W` begins a basis of `W` indexed by `Fin (n+1)`. -/
theorem exists_indep_first {W : Submodule F V} {n : ℕ} (hn : finrank F W = n + 1) {v : V} (hv : v ∈ W)
    (hv0 : v ≠ 0) :
    ∃ x : Fin (n + 1) → V, LinearIndependent F x ∧ span F (Set.range x) = W ∧ x 0 = v := by
  have : FiniteDimensional F W := Module.finite_of_finrank_pos (by omega)
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (span F {v})
  set U : Submodule F V := C ⊓ W with hU
  have hUW : U ≤ W := inf_le_right
  have : FiniteDimensional F U := Submodule.finiteDimensional_of_le hUW
  have hvW : span F {v} ≤ W := (Submodule.span_singleton_le_iff_mem _ _).mpr hv
  have hsup : span F {v} ⊔ U = W := by
    have := sup_inf_assoc_of_le C hvW
    rw [hC.sup_eq_top, top_inf_eq] at this
    exact this.symm
  have hdisj : span F {v} ⊓ U = ⊥ := by
    apply eq_bot_iff.mpr
    calc span F {v} ⊓ U ≤ span F {v} ⊓ C := inf_le_inf_left _ inf_le_left
      _ = ⊥ := hC.inf_eq_bot
      _ ≤ ⊥ := le_rfl
  have hvU : v ∉ U := by
    intro h
    have : v ∈ span F {v} ⊓ U := ⟨Submodule.mem_span_singleton_self v, h⟩
    rw [hdisj] at this
    exact hv0 (by simpa using this)
  have hfin := Submodule.finrank_sup_add_finrank_inf_eq (span F {v}) U
  rw [hsup, hdisj, finrank_span_singleton hv0, finrank_bot, hn] at hfin
  have hUn : finrank F U = n := by omega
  let b := Module.finBasisOfFinrankEq F U hUn
  let g : Fin n → V := fun i => (b i : V)
  have hg : LinearIndependent F g := b.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
  have hgU : ∀ i, g i ∈ U := fun i => (b i).2
  have hli : LinearIndependent F (Fin.cons v g : Fin (n + 1) → V) := by
    refine linearIndependent_finCons.mpr ⟨hg, fun h => hvU ?_⟩
    exact (span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hgU i) : span F (Set.range g) ≤ U) h
  refine ⟨Fin.cons v g, hli, ?_, by simp⟩
  apply Submodule.eq_of_le_of_finrank_eq
  · refine span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hv
    · simpa using hUW (hgU j)
  · rw [finrank_span_eq_card hli, hn]; simp

/-- Coefficients are monotone in the lattice. -/
theorem coeff_mono {L K : Submodule R V} (h : K ≤ L) (v : V) : coeff F K v ≤ coeff F L v :=
  fun _ hα => h hα

/-- The ratio `𝔞_v(K) 𝔞_v(L)⁻¹` of the coefficients of `v` (O'Meara's `𝔱` for a vector). -/
def tau (F : Type*) [Field F] [Algebra R F] [Module F V] [IsScalarTower R F V] (L K : Submodule R V)
    (v : V) : Submodule R F :=
  coeff F K v * (1 / coeff F L v)

/-- `τ(v)` is an integral ideal when `K ≤ L`. -/
theorem tau_le_one {L K : Submodule R V} (hL : L.FG) (hKL : K ≤ L) {v : V}
    (hv : v ∈ span F (L : Set V)) (hv0 : v ≠ 0) : tau F L K v ≤ 1 := by
  have hfi : (coeff F L v).FG ∧ coeff F L v ≠ ⊥ := ⟨coeff_fg hL hv0, coeff_ne_bot hv⟩
  calc tau F L K v ≤ coeff F L v * (1 / coeff F L v) := mul_le_mul' (coeff_mono hKL v) le_rfl
    _ = 1 := fi_mul_one_div hfi

/-- A vector `v` of `FL` and a hyperplane `U` of `FL` complementary to `v` on which `v` has the largest
coefficient (step 1 of the proof of 81:11, via 81:3). -/
theorem exists_hyperplane {L : Submodule R V} (hL : L.FG) {n : ℕ}
    (hn : finrank F (span F (L : Set V)) = n + 1) {v : V} (hv : v ∈ span F (L : Set V)) (hv0 : v ≠ 0) :
    ∃ U : Submodule F V, v ∉ U ∧ U ≤ span F (L : Set V) ∧ span F (L : Set V) ≤ U ⊔ span F {v} ∧
      finrank F U = n ∧ ∀ u ∈ U, coeff F L (v + u) ≤ coeff F L v := by
  classical
  have : FiniteDimensional F (span F (L : Set V)) := Module.finite_of_finrank_pos (by omega)
  obtain ⟨x, hx, hxspan, hx0⟩ := exists_indep_first hn hv hv0
  obtain ⟨y, hy, hyf, a, ha, hLeq⟩ := exists_adapted_flag hL x hx hxspan
  have hyW : ∀ i, y i ∈ span F (L : Set V) := fun i => by
    rw [← hxspan]; exact span_mono (Set.image_subset_range _ _) (hyf i)
  have hy0 : ∃ c : F, y 0 = c • v := by
    have := hyf 0
    have hI : (x '' Set.Iic (0 : Fin (n + 1))) = {v} := by
      ext z
      simp [hx0, eq_comm]
    rw [hI] at this
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp this
    exact ⟨c, hc.symm⟩
  obtain ⟨c, hc⟩ := hy0
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hy.ne_zero 0 (by simpa using hc)
  set U : Submodule F V := span F (Set.range fun i : Fin n => y i.succ) with hU
  have hycons : LinearIndependent F (Fin.cons (y 0) (fun i : Fin n => y i.succ) : Fin (n + 1) → V) := by
    have : (Fin.cons (y 0) (fun i : Fin n => y i.succ) : Fin (n + 1) → V) = y := Fin.cons_self_tail y
    rw [this]; exact hy
  have hy0U : y 0 ∉ U := (linearIndependent_finCons.mp hycons).2
  have hvU : v ∉ U := by
    intro h
    apply hy0U
    rw [hc]; exact U.smul_mem c h
  have hUW : U ≤ span F (L : Set V) := span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hyW _)
  have hUfin : finrank F U = n := by
    rw [hU, finrank_span_eq_card (linearIndependent_finCons.mp hycons).1]; simp
  have hspany : span F (Set.range y) = span F (L : Set V) := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hyW _)
    · rw [finrank_span_eq_card hy, hn]; simp
  refine ⟨U, hvU, hUW, ?_, hUfin, ?_⟩
  · rw [← hspany]
    refine span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [hc]; exact Submodule.mem_sup_right (Submodule.smul_mem _ _ (mem_span_singleton_self v))
    · exact Submodule.mem_sup_left (subset_span ⟨j, rfl⟩)
  · intro u hu γ hγ
    rw [mem_coeff] at hγ ⊢
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hu
    have hv' : v = c⁻¹ • y 0 := by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    set e : Fin (n + 1) → F := Fin.cons (γ * c⁻¹) (fun i => γ * d i) with he
    have hsum : γ • (v + u) = ∑ j, e j • y j := by
      rw [Fin.sum_univ_succ, smul_add, ← hd]
      simp only [he, Fin.cons_zero, Fin.cons_succ]
      rw [Finset.smul_sum]
      congr 1
      · rw [hv', smul_smul]
      · exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]
    rw [hLeq, hsum] at hγ
    have h0 := coord_mem_of_mem_iSup hy a e hγ 0
    have : γ • v = (γ * c⁻¹) • y 0 := by rw [hv', smul_smul]
    rw [this, hLeq]
    exact (smul_mem_iSup_iff hy a 0 _).mpr (by simpa [he] using h0)

/-- `𝔞_v(K) = 𝔞_v(L) τ(v)`. -/
theorem coeff_eq_mul_tau {L K : Submodule R V} {v : V} (hA : (coeff F L v).FG ∧ coeff F L v ≠ ⊥) :
    coeff F L v * tau F L K v = coeff F K v := by
  unfold tau
  calc coeff F L v * (coeff F K v * (1 / coeff F L v))
      = coeff F K v * (coeff F L v * (1 / coeff F L v)) := by ring
    _ = coeff F K v := by rw [fi_mul_one_div hA, mul_one]

/-- **Step 4 of the proof of 81:11**: if `τ(v)` is maximal then `𝔱_k ⊆ τ(v)` for the invariant factors
`𝔱_k` of the hyperplane `U`. -/
theorem t_le_tau {L K : Submodule R V} (hL : L.FG) (hKL : K ≤ L)
    (hspan : span F (K : Set V) = span F (L : Set V)) {U : Submodule F V} {v : V}
    (hvW : v ∈ span F (L : Set V)) (hvU : v ∉ U) (hUW : U ≤ span F (L : Set V))
    (hdecL : L = coeff F L v • span R {v} ⊔ (L ⊓ U.restrictScalars R))
    {n : ℕ} {w : Fin n → V} (hw : LinearIndependent F w) (hwU : ∀ i, w i ∈ U)
    {a t : Fin n → Submodule R F} (ha : ∀ i, (a i).FG ∧ a i ≠ ⊥) (ht : ∀ i, (t i).FG ∧ t i ≠ ⊥)
    (hLU : L ⊓ U.restrictScalars R = ⨆ i, a i • span R {w i})
    (hKU : K ⊓ U.restrictScalars R = ⨆ i, (a i * t i) • span R {w i})
    (hmax : ∀ v' ∈ span F (L : Set V), v' ≠ 0 → ¬ tau F L K v < tau F L K v') (k : Fin n) :
    t k ≤ tau F L K v := by
  classical
  have hv0 : v ≠ 0 := fun h => hvU (h ▸ U.zero_mem)
  have hKfg : K.FG := fg_of_le_aux hL hKL
  have hA1 : (coeff F L v).FG ∧ coeff F L v ≠ ⊥ := ⟨coeff_fg hL hv0, coeff_ne_bot hvW⟩
  have hvK : v ∈ span F (K : Set V) := by rw [hspan]; exact hvW
  have hT1fi : (tau F L K v).FG ∧ tau F L K v ≠ ⊥ :=
    fi_mul ⟨coeff_fg hKfg hv0, coeff_ne_bot hvK⟩ (fi_one_div hA1)
  obtain ⟨α, β, hα0, hαmem, hβmem, hcop⟩ := exists_coprime_pair hA1 (ha k) hT1fi (ht k)
  set z := α • v + β • w k with hz
  have hzU : z ∉ U := by
    intro h
    apply hvU
    have h2 : α • v ∈ U := by
      have := U.sub_mem h (U.smul_mem β (hwU k))
      rwa [hz, add_sub_cancel_right] at this
    have := U.smul_mem α⁻¹ h2
    rwa [smul_smul, inv_mul_cancel₀ hα0, one_smul] at this
  have hz0 : z ≠ 0 := fun h => hzU (h ▸ U.zero_mem)
  have hzW : z ∈ span F (L : Set V) :=
    add_mem (Submodule.smul_mem _ _ hvW) (Submodule.smul_mem _ _ (hUW (hwU k)))
  have hαK : α • v ∈ K := by
    have : α ∈ coeff F K v := by rw [← coeff_eq_mul_tau (K := K) hA1]; exact hαmem
    exact this
  have hβK : β • w k ∈ K := by
    have h1 : β • w k ∈ K ⊓ U.restrictScalars R := by
      rw [hKU]; exact (smul_mem_iSup_iff hw _ k β).mpr hβmem
    exact h1.1
  have hzK : z ∈ K := K.add_mem hαK hβK
  have hcoeffLz : coeff F L z ≤ 1 / (tau F L K v ⊔ t k) := by
    intro γ hγ
    apply hcop γ
    · have hγ' : γ • z ∈ L := hγ
      have hsplit : γ • z = (γ * α) • v + (γ * β) • w k := by
        rw [hz, smul_add, smul_smul, smul_smul]
      rw [hsplit] at hγ'
      exact (mem_and_mem_of_dec hvU hdecL (U.smul_mem _ (hwU k)) hγ').1
    · have hγ' : γ • z ∈ L := hγ
      have hsplit : γ • z = (γ * α) • v + (γ * β) • w k := by
        rw [hz, smul_add, smul_smul, smul_smul]
      rw [hsplit] at hγ'
      have h2 := (mem_and_mem_of_dec hvU hdecL (U.smul_mem _ (hwU k)) hγ').2
      have h3 : (γ * β) • w k ∈ L ⊓ U.restrictScalars R := ⟨h2, U.smul_mem _ (hwU k)⟩
      rw [hLU] at h3
      exact (smul_mem_iSup_iff hw _ k _).mp h3
  have hBfi : (coeff F L z).FG ∧ coeff F L z ≠ ⊥ := ⟨coeff_fg hL hz0, coeff_ne_bot hzW⟩
  have hSfi := fi_sup hT1fi (ht k)
  have h1 := fi_one_div_le hBfi (fi_one_div hSfi) hcoeffLz
  rw [fi_one_div_one_div hSfi] at h1
  have hStau : tau F L K v ⊔ t k ≤ tau F L K z :=
    calc tau F L K v ⊔ t k ≤ 1 / coeff F L z := h1
      _ = 1 * (1 / coeff F L z) := (one_mul _).symm
      _ ≤ coeff F K z * (1 / coeff F L z) := mul_le_mul' (one_le_coeff_iff.mpr hzK) le_rfl
  have heq : tau F L K v = tau F L K z := by
    by_contra hne
    exact hmax z hzW hz0 (lt_of_le_of_ne (le_sup_left.trans hStau) hne)
  exact le_sup_right.trans (hStau.trans heq.ge)

/-- **Step 3 of the proof of 81:11**: if `τ(v)` is maximal then `v` has the largest `K`-coefficient on
`v + U`, so `K = 𝔞_v(K) v + (K ∩ U)`. -/
theorem decomp_of_tau_max {L K : Submodule R V} (hL : L.FG) (hKL : K ≤ L)
    (hspan : span F (K : Set V) = span F (L : Set V)) {U : Submodule F V} {v : V}
    (hvW : v ∈ span F (L : Set V)) (hvU : v ∉ U) (hUW : U ≤ span F (L : Set V))
    (hWU : span F (L : Set V) ≤ U ⊔ span F {v})
    (hLv : ∀ u ∈ U, coeff F L (v + u) ≤ coeff F L v)
    (hmax : ∀ v' ∈ span F (L : Set V), v' ≠ 0 → ¬ tau F L K v < tau F L K v') :
    K = coeff F K v • span R {v} ⊔ (K ⊓ U.restrictScalars R) := by
  have hKfg : K.FG := fg_of_le_aux hL hKL
  have hKU : ∀ x ∈ K, x ∈ U ⊔ span F {v} := fun x hx =>
    hWU (by rw [← hspan]; exact subset_span hx)
  have hv0 : v ≠ 0 := fun h => hvU (h ▸ U.zero_mem)
  have hclaim : ∀ u ∈ U, coeff F K (v + u) ≤ coeff F K v := by
    by_contra hcon
    simp only [not_forall] at hcon
    obtain ⟨u₁, hu₁, hu₁'⟩ := hcon
    obtain ⟨u₀, hu₀, hu₀max⟩ := exists_coeff_max hKfg hvU hKU
    have hle : coeff F K v ≤ coeff F K (v + u₀) := by
      simpa using hu₀max 0 U.zero_mem
    have hlt : coeff F K v < coeff F K (v + u₀) := by
      refine lt_of_le_of_ne hle fun he => hu₁' ?_
      rw [he]; exact hu₀max u₁ hu₁
    have hzW : v + u₀ ∈ span F (L : Set V) := add_mem hvW (hUW hu₀)
    have hz0 : v + u₀ ≠ 0 := by
      intro h
      apply hvU
      have : v = -u₀ := eq_neg_of_add_eq_zero_left h
      rw [this]; exact U.neg_mem hu₀
    have hFz : (coeff F L (v + u₀)).FG ∧ coeff F L (v + u₀) ≠ ⊥ :=
      ⟨coeff_fg hL hz0, coeff_ne_bot hzW⟩
    have hFv : (coeff F L v).FG ∧ coeff F L v ≠ ⊥ := ⟨coeff_fg hL hv0, coeff_ne_bot hvW⟩
    have h1 : 1 / coeff F L v ≤ 1 / coeff F L (v + u₀) := fi_one_div_le hFz hFv (hLv u₀ hu₀)
    apply hmax (v + u₀) hzW hz0
    unfold tau
    exact lt_of_le_of_lt (mul_le_mul' le_rfl h1) (fi_mul_lt_mul (fi_one_div hFz) hlt)
  have := eq_coeff_smul_sup_inf (L := K) (u₀ := 0) hKU U.zero_mem (by simpa using hclaim)
  simpa using this

/-- A finitely generated `R`-submodule spans a finite-dimensional `F`-space. -/
theorem finiteDimensional_span_of_fg {L : Submodule R V} (hL : L.FG) :
    FiniteDimensional F (span F (L : Set V)) := by
  obtain ⟨S, rfl⟩ := hL
  rw [Submodule.span_span_of_tower]
  exact FiniteDimensional.span_of_finite F S.finite_toSet

/-- The span of `M ∩ U` is `U` when `U ⊆ FM`. -/
theorem span_inf_eq_of_le {M : Submodule R V} {U : Submodule F V} (hU : U ≤ span F (M : Set V)) :
    span F ((M ⊓ U.restrictScalars R : Submodule R V) : Set V) = U := by
  apply le_antisymm
  · exact span_le.mpr fun v hv => hv.2
  · intro u hu
    obtain ⟨d, hd0, hd⟩ := exists_smul_mem_of_mem_span (F := F) (hU hu)
    have hdu : d • u ∈ (M ⊓ U.restrictScalars R : Submodule R V) :=
      ⟨hd, (U.smul_of_tower_mem d hu : d • u ∈ U)⟩
    have hd' : algebraMap R F d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hd0
    have : u = (algebraMap R F d)⁻¹ • (d • u) := by
      rw [← algebraMap_smul F d u, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (subset_span hdu)

/-- `τ(v)` is a fractional ideal. -/
theorem tau_fi {L K : Submodule R V} (hL : L.FG) (hKL : K ≤ L)
    (hspan : span F (K : Set V) = span F (L : Set V)) {v : V} (hv : v ∈ span F (L : Set V)) (hv0 : v ≠ 0) :
    (tau F L K v).FG ∧ tau F L K v ≠ ⊥ :=
  fi_mul ⟨coeff_fg (fg_of_le_aux hL hKL) hv0, coeff_ne_bot (by rw [hspan]; exact hv)⟩
    (fi_one_div ⟨coeff_fg hL hv0, coeff_ne_bot hv⟩)

/-- Prepending a larger element to an antitone family keeps it antitone. -/
theorem antitone_cons_aux {n : ℕ} {M : Type*} [Preorder M] (t' : Fin n → M) (τ : M) (h : ∀ k, t' k ≤ τ)
    (hanti : Antitone t') : Antitone (Fin.cons τ t' : Fin (n + 1) → M) := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact le_rfl
    | succ j' => simpa using h j'
  | succ i' =>
    cases j using Fin.cases with
    | zero => exact absurd hij (by simp)
    | succ j' => simpa using hanti (Fin.succ_le_succ_iff.mp hij)

/-- **Theorem 81:11, existence** (O'Meara 1963, pp. 214–215), for lattices $K \subseteq L$ spanning the same
$n$-dimensional space $W$. There are a base $x_1, \dots, x_n$ of $W$ and fractional ideals $\mathfrak a_i$,
$\mathfrak t_i$ with $\mathfrak t_1 \supseteq \cdots \supseteq \mathfrak t_n$ such that
$L = \mathfrak a_1x_1 + \cdots + \mathfrak a_nx_n$ and $K = \mathfrak a_1\mathfrak t_1x_1 + \cdots +
\mathfrak a_n\mathfrak t_nx_n$. -/
@[kb "omeara1963" "§81D, 81:11, pp. 214–215 (existence of the invariant factors)"]
theorem exists_invariant_factors_of_le {n : ℕ} {L K : Submodule R V} (hL : L.FG) (hKL : K ≤ L)
    (hspan : span F (K : Set V) = span F (L : Set V)) (hn : finrank F (span F (L : Set V)) = n) :
    ∃ x : Fin n → V, LinearIndependent F x ∧ span F (Set.range x) = span F (L : Set V) ∧
      ∃ a t : Fin n → Submodule R F, (∀ i, (a i).FG ∧ a i ≠ ⊥) ∧ (∀ i, (t i).FG ∧ t i ≠ ⊥) ∧ Antitone t ∧
        L = ⨆ i, a i • span R {x i} ∧ K = ⨆ i, (a i * t i) • span R {x i} := by
  classical
  have hfd := finiteDimensional_span_of_fg (F := F) hL
  induction n generalizing L K with
  | zero =>
    have hW : span F (L : Set V) = ⊥ := Submodule.finrank_eq_zero.mp hn
    have hL0 : L = ⊥ := by
      rw [eq_bot_iff]
      intro l hl
      have : l ∈ span F (L : Set V) := subset_span hl
      rw [hW] at this
      simpa using this
    have hK0 : K = ⊥ := le_bot_iff.mp (hL0 ▸ hKL)
    refine ⟨fun i => i.elim0, linearIndependent_empty_type, ?_, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, ?_, ?_⟩
    · rw [hW]; simp
    · simp [hL0]
    · simp [hK0]
  | succ n ih =>
    set W : Submodule F V := span F (L : Set V) with hWdef
    have hWne : W ≠ ⊥ := by
      intro h
      rw [h] at hn
      simp at hn
    obtain ⟨v₁, hv₁W, hv₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
    obtain ⟨v, ⟨hvW, hv0⟩, hvmax⟩ := exists_tau_max {v | v ∈ W ∧ v ≠ 0} ⟨v₁, hv₁W, hv₁0⟩
      (tau F L K) (fun v hv => tau_le_one hL hKL hv.1 hv.2)
    have hmax : ∀ v' ∈ W, v' ≠ 0 → ¬ tau F L K v < tau F L K v' := fun v' h1 h2 => hvmax v' ⟨h1, h2⟩
    obtain ⟨U, hvU, hUW, hWU, hUn, hLv⟩ := exists_hyperplane hL hn hvW hv0
    have hLU : ∀ x ∈ L, x ∈ U ⊔ span F {v} := fun x hx => hWU (subset_span hx)
    have hdecL : L = coeff F L v • span R {v} ⊔ (L ⊓ U.restrictScalars R) := by
      have := eq_coeff_smul_sup_inf (L := L) (u₀ := 0) hLU U.zero_mem (by simpa using hLv)
      simpa using this
    have hdecK := decomp_of_tau_max hL hKL hspan hvW hvU hUW hWU hLv hmax
    have hL'fg : (L ⊓ U.restrictScalars R).FG := fg_of_le_aux hL inf_le_left
    have hK'L' : K ⊓ U.restrictScalars R ≤ L ⊓ U.restrictScalars R := inf_le_inf_right _ hKL
    have hspanL' : span F ((L ⊓ U.restrictScalars R : Submodule R V) : Set V) = U :=
      span_inf_eq_of_le hUW
    have hspanK' : span F ((K ⊓ U.restrictScalars R : Submodule R V) : Set V) = U :=
      span_inf_eq_of_le (by rw [hspan]; exact hUW)
    obtain ⟨w, hw, hwspan, a', t', ha', ht', hanti', hL'eq, hK'eq⟩ :=
      ih hL'fg hK'L' (by rw [hspanK', hspanL']) (by rw [hspanL', hUn])
        (finiteDimensional_span_of_fg hL'fg)
    rw [hspanL'] at hwspan
    have hwU : ∀ i, w i ∈ U := fun i => hwspan ▸ subset_span ⟨i, rfl⟩
    have hT1fi := tau_fi hL hKL hspan hvW hv0
    have hA1 : (coeff F L v).FG ∧ coeff F L v ≠ ⊥ := ⟨coeff_fg hL hv0, coeff_ne_bot hvW⟩
    have hli : LinearIndependent F (Fin.cons v w : Fin (n + 1) → V) := by
      refine linearIndependent_finCons.mpr ⟨hw, fun h => hvU ?_⟩
      rw [← hwspan]; exact h
    refine ⟨Fin.cons v w, hli, ?_, Fin.cons (coeff F L v) a', Fin.cons (tau F L K v) t', ?_, ?_, ?_, ?_, ?_⟩
    · rw [Fin.range_cons, Submodule.span_insert, hwspan, sup_comm]
      apply le_antisymm
      · exact sup_le (hUW) (by rw [Submodule.span_singleton_le_iff_mem]; exact hvW)
      · exact hWU
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hA1
      · simpa using ha' j
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hT1fi
      · simpa using ht' j
    · exact antitone_cons_aux t' _ (t_le_tau hL hKL hspan hvW hvU hUW hdecL hw hwU ha' ht' hL'eq hK'eq hmax)
        hanti'
    · rw [iSup_cons_aux]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← hL'eq]
      exact hdecL
    · rw [iSup_cons_aux]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← hK'eq, coeff_eq_mul_tau hA1]
      exact hdecK

/-- **Theorem 81:11, existence** (O'Meara 1963, pp. 214–215), as stated. Given lattices $L$ and $K$ on the vector
space $V$, there is a base $x_1, \dots, x_n$ of $V$ in which $L = \mathfrak a_1x_1 + \cdots + \mathfrak a_nx_n$ and
$K = \mathfrak a_1\mathfrak t_1x_1 + \cdots + \mathfrak a_n\mathfrak t_nx_n$ with fractional ideals $\mathfrak a_i$,
$\mathfrak t_i$ and $\mathfrak t_1 \supseteq \cdots \supseteq \mathfrak t_n$. (O'Meara assumes $V \ne 0$; for $V = 0$
the statement is empty.) -/
@[kb "omeara1963" "§81D, 81:11, pp. 214–215 (existence of the invariant factors)"]
theorem exists_invariant_factors [FiniteDimensional F V] {L K : Submodule R V} (hL : L.IsLattice F)
    (hK : K.IsLattice F) :
    ∃ x : Basis (Fin (finrank F V)) F V, ∃ a t : Fin (finrank F V) → Submodule R F,
      (∀ i, (a i).FG ∧ a i ≠ ⊥) ∧ (∀ i, (t i).FG ∧ t i ≠ ⊥) ∧ Antitone t ∧
        L = ⨆ i, a i • span R {x i} ∧ K = ⨆ i, (a i * t i) • span R {x i} := by
  classical
  have htf := isTorsionFree_of_fractionRing (R := R) (F := F) (V := V)
  obtain ⟨d, hd0, hd⟩ := (fg_iff_exists_smul_le hL K).mp hK.fg
  have hd' : algebraMap R F d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hd0
  set K' : Submodule R V := K.map (LinearMap.lsmul R V d) with hK'def
  have hK'L : K' ≤ L := by
    rintro _ ⟨k, hk, rfl⟩
    exact hd k hk
  have hspanK' : span F (K' : Set V) = span F (L : Set V) := by
    rw [hL.span_eq_top, eq_top_iff, ← hK.span_eq_top]
    refine span_le.mpr fun k hk => ?_
    have : k = (algebraMap R F d)⁻¹ • (d • k) := by
      rw [← algebraMap_smul F d k, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (subset_span ⟨k, hk, rfl⟩)
  have hn : finrank F (span F (L : Set V)) = finrank F V := by
    rw [hL.span_eq_top]; exact finrank_top F V
  obtain ⟨x, hx, hxspan, a, t, ha, ht, hanti, hLeq, hK'eq⟩ :=
    exists_invariant_factors_of_le hL.fg hK'L hspanK' hn
  have hsp : ⊤ ≤ span F (Set.range x) := by rw [hxspan, hL.span_eq_top]
  set b : Basis (Fin (finrank F V)) F V := Basis.mk hx hsp with hb
  have hbx : ∀ i, b i = x i := fun i => by simp [hb]
  have hcfi : (span R {(algebraMap R F d)⁻¹}).FG ∧ span R {(algebraMap R F d)⁻¹} ≠ ⊥ :=
    ⟨Submodule.fg_span_singleton _, by simpa using inv_ne_zero hd'⟩
  have key : ∀ v, v ∈ K ↔ ∀ i, b.repr v i ∈ span R {(algebraMap R F d)⁻¹} * (a i * t i) := by
    intro v
    have h1 : v ∈ K ↔ d • v ∈ K' := by
      constructor
      · intro hv; exact ⟨v, hv, rfl⟩
      · rintro ⟨k, hk, hkv⟩
        have : k = v := smul_right_injective V hd0 hkv
        rw [← this]; exact hk
    rw [h1, hK'eq]
    simp only [← hbx]
    rw [mem_iSup_smul_span_iff]
    refine forall_congr' fun i => ?_
    rw [← algebraMap_smul F d v, map_smul, Finsupp.smul_apply, smul_eq_mul,
      Submodule.mem_span_singleton_mul]
    constructor
    · intro h
      exact ⟨_, h, by field_simp⟩
    · rintro ⟨z, hz, hzr⟩
      rw [← hzr, mul_inv_cancel_left₀ hd']
      exact hz
  refine ⟨b, a, fun i => t i * span R {(algebraMap R F d)⁻¹}, ha, fun i => fi_mul (ht i) hcfi,
    fun i j hij => mul_le_mul' (hanti hij) le_rfl, ?_, ?_⟩
  · simp only [hbx]; exact hLeq
  · ext v
    rw [key, mem_iSup_smul_span_iff]
    refine forall_congr' fun i => ?_
    rw [show a i * (t i * span R {(algebraMap R F d)⁻¹}) = span R {(algebraMap R F d)⁻¹} * (a i * t i) by ring]

end QuadFormsKB.OMeara
