/-
# O'Meara §101C: a local step in the proof of Lemma 101:11

**Layer:** $F$ a number field, $v$ a finite spot of $F$ not dividing $2$, $F_v$ = `v.adicCompletion F`,
$Q = \langle \alpha_0, \dots, \alpha_{m-1} \rangle$ a diagonal form with all $\alpha_i \in F^\times$ (`QuadForm.diag α`),
$X \subseteq F$ finite consisting of $v$-units and $0$; `RegTernaryRepresents` (`Sec101Named.lean`).

**Proves**
* `regTernaryRepresents_units_nondyadic` (step 2 of the proof of **Lemma 101:11**, O'Meara p. 294): if $m \ge 4$,
  $v \nmid 2$, and every non-zero $a \in X$ has $v(a) = 1$, then some regular ternary subspace of $F_v^m$ represents
  every element of $X$. Proof: let $o_i = \operatorname{ord}_v \alpha_i$. If for some three of the indices $0,1,2,3$
  the sum of the $o_i$ is odd, say for $i,j,k$, then for a unit $a$ the form $\langle \alpha_i,\alpha_j,\alpha_k,-a\rangle$
  has determinant of odd order, hence non-square in $F_v$, hence is isotropic (`isotropic_four_of_not_isSquare`), and
  an isotropic ternary form is universal; so the ternary form $\langle \alpha_i,\alpha_j,\alpha_k\rangle$ represents $a$.
  Otherwise all four $o_i$ have the same parity, which is therefore even; then $\alpha_i = u_i t_i^2$ with $u_i$ a
  $v$-unit and $\langle u_0,u_1,u_2\rangle$ is isotropic (`NFLocal.isotropic_diag_units_nf`, using $v \nmid 2$), so
  $\langle \alpha_0,\alpha_1,\alpha_2\rangle$ is isotropic and universal.
  The subspace is a coordinate subspace (`regTernaryRepresents_of_coordinates`).

*Convention:* indices are 0-based; O'Meara's $\alpha_1, \dots, \alpha_4$ are `α 0`, …, `α 3`.
-/
import QuadFormsKB.Literature.OMeara.Sec101Named
import QuadFormsKB.Tamagawa.LocalRankFive
import QuadFormsKB.Literature.LocalGlobal.NumberFieldLocal
import QuadFormsKB.Witt.Represents
import QuadFormsKB.Lattices.Local

open NumberField IsDedekindDomain WithZero
open scoped Matrix

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace QuadFormsKB.Lattices

/-- The integer $k$ with $v(x) = e^{k}$ for $x \in F$ ($-\operatorname{ord}_v x$; the junk value $0$ at $x = 0$); a
local notation for `WithZero.log (v.valuation F x)` (on units it is `SqDual.ordL`). -/
local notation "ordv " v:max x:max => WithZero.log (IsDedekindDomain.HeightOneSpectrum.valuation _ v x)

variable {F : Type} [Field F] [NumberField F]

/-! ### Coordinate subspaces -/

section Coordinates

variable {K : Type*} [Field K] [Algebra F K] {m : ℕ}

/-- Extension by zero along an injective `f : Fin 3 → Fin m`, as a $K$-linear map $K^3 \to K^m$. -/
def extendLin (f : Fin 3 → Fin m) (hf : Function.Injective f) : (Fin 3 → K) →ₗ[K] (Fin m → K) where
  toFun y := Function.extend f y 0
  map_add' y y' := by
    funext i
    by_cases h : ∃ k, f k = i
    · obtain ⟨k, rfl⟩ := h
      simp [hf.extend_apply]
    · simp [Function.extend_apply' _ _ _ h]
  map_smul' c y := by
    funext i
    by_cases h : ∃ k, f k = i
    · obtain ⟨k, rfl⟩ := h
      simp [hf.extend_apply]
    · simp [Function.extend_apply' _ _ _ h]

theorem extendLin_apply (f : Fin 3 → Fin m) (hf : Function.Injective f) (y : Fin 3 → K) (k : Fin 3) :
    extendLin f hf y (f k) = y k := hf.extend_apply _ _ _

theorem extendLin_apply_of_not (f : Fin 3 → Fin m) (hf : Function.Injective f) (y : Fin 3 → K) {i : Fin m}
    (h : ¬ ∃ k, f k = i) : extendLin f hf y i = 0 := by
  simp [extendLin, Function.extend_apply' _ _ _ h]

theorem extendLin_injective (f : Fin 3 → Fin m) (hf : Function.Injective f) :
    Function.Injective (extendLin (K := K) f hf) := by
  intro y y' h
  funext k
  have := congrFun h (f k)
  rwa [extendLin_apply, extendLin_apply] at this

/-- Sums over $\{0,\dots,m-1\}$ of terms supported on the image of `f` become sums over `Fin 3`. -/
theorem sum_extendLin (f : Fin 3 → Fin m) (hf : Function.Injective f) (g : Fin m → K)
    (h0 : ∀ i, (¬ ∃ k, f k = i) → g i = 0) : ∑ i, g i = ∑ k, g (f k) :=
  (Fintype.sum_of_injective f hf (fun k => g (f k)) g (fun i hi => h0 i (by simpa using hi))
    (fun _ => rfl)).symm

/-- The Hessian of $\langle \alpha_0, \dots, \alpha_{m-1}\rangle$ acts by $y \mapsto (2\alpha_i y_i)_i$. -/
theorem hessian_diag_mulVec (α : Fin m → F) (y : Fin m → K) (i : Fin m) :
    ((QuadForm.diag α).hessian.map (algebraMap F K) *ᵥ y) i = 2 * algebraMap F K (α i) * y i := by
  simp only [QuadForm.hessian, QuadForm.diag, Matrix.diagonal_transpose, Matrix.diagonal_add]
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
  · simp [Matrix.diagonal_apply_eq]; left; ring
  · intro j _ hj; simp [Matrix.map_apply, Matrix.diagonal_apply_ne _ (Ne.symm hj)]
  · simp

/-- **A ternary form on coordinates that represents $X$ gives a regular ternary subspace.** If
$\langle \alpha_{f(0)}, \alpha_{f(1)}, \alpha_{f(2)}\rangle$ represents every $a \in X$ over $K$ for an injective
`f : Fin 3 → Fin m` and all $\alpha_i \ne 0$, then $\langle \alpha_0,\dots,\alpha_{m-1}\rangle$ has a regular ternary
subspace over $K$ (the span of the coordinate vectors $e_{f(0)}, e_{f(1)}, e_{f(2)}$) representing $X$. -/
theorem regTernaryRepresents_of_coordinates [CharZero K] (α : Fin m → F) (hα : ∀ i, α i ≠ 0)
    (X : Finset F) (f : Fin 3 → Fin m) (hf : Function.Injective f)
    (hrep : ∀ a ∈ X, (QuadForm.diag (α ∘ f)).RepresentsIn K a) :
    RegTernaryRepresents (QuadForm.diag α) K X := by
  have hα' : ∀ i, algebraMap F K (α i) ≠ 0 := fun i =>
    (map_ne_zero_iff _ (algebraMap F K).injective).2 (hα i)
  -- pairing of two extended vectors
  have pair : ∀ y y' : Fin 3 → K,
      extendLin f hf y ⬝ᵥ ((QuadForm.diag α).hessian.map (algebraMap F K) *ᵥ extendLin f hf y') =
        ∑ k, 2 * algebraMap F K (α (f k)) * y k * y' k := by
    intro y y'
    simp only [dotProduct, hessian_diag_mulVec]
    rw [sum_extendLin f hf]
    · simp [extendLin_apply]; exact Finset.sum_congr rfl fun k _ => by ring
    · intro i hi; simp [extendLin_apply_of_not f hf _ hi]
  refine ⟨LinearMap.range (extendLin (K := K) f hf), ?_, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj (extendLin_injective f hf)]; simp
  · rintro x ⟨y, rfl⟩ hx
    have : y = 0 := by
      funext k
      have h := hx (extendLin f hf (Pi.single k 1)) ⟨_, rfl⟩
      rw [pair] at h
      rw [Finset.sum_eq_single k] at h
      · rw [Pi.single_eq_same, mul_one] at h
        rcases mul_eq_zero.1 h with h3 | h3
        · rcases mul_eq_zero.1 h3 with h4 | h4
          · exact absurd h4 two_ne_zero
          · exact absurd h4 (hα' _)
        · exact h3
      · intro j _ hj; simp [hj]
      · simp
    simp [this]
  · intro a ha
    obtain ⟨y, hy⟩ := hrep a ha
    refine ⟨extendLin f hf y, ⟨y, rfl⟩, ?_⟩
    rw [← hy, QuadForm.evalIn_diag, QuadForm.evalIn_diag, sum_extendLin f hf]
    · simp [extendLin_apply]
    · intro i hi; simp [extendLin_apply_of_not f hf _ hi]

end Coordinates

/-! ### Orders at $v$ and universality -/

section Local

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Kv" => v.adicCompletion F


theorem ordv_mul {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) : ordv v (x * y) = ordv v x + ordv v y := by
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).mpr hx) ((Valuation.ne_zero_iff _).mpr hy)]

theorem ordv_neg_of_unit {a : F} (ha : v.valuation F a = 1) : ordv v (-a) = 0 := by
  simp [ha]

/-- **An element of $F^\times$ of odd order at $v$ is not a square in $F_v$.** -/
theorem not_isSquare_of_odd {x : F} (hx : x ≠ 0) (h : ¬ Even (ordv v x)) :
    ¬ IsSquare (algebraMap F Kv x) := by
  rintro ⟨s, hs⟩
  have hs0 : Valued.v s ≠ 0 := by
    intro h0
    have : s = 0 := (Valuation.zero_iff _).1 h0
    apply hx
    have : algebraMap F Kv x = 0 := by rw [hs, this, mul_zero]
    exact (map_eq_zero_iff _ (algebraMap F Kv).injective).1 this
  apply h
  have h1 : v.valuation F x = Valued.v s * Valued.v s := by
    rw [← valued_algebraMap, hs, map_mul]
  exact ⟨WithZero.log (Valued.v s), by rw [h1, WithZero.log_mul hs0 hs0]⟩

/-- **An isotropic diagonal ternary form is universal:** if $\langle \beta_0,\beta_1,\beta_2\rangle$ with
$\beta_i \in F^\times$ is isotropic over $K$, it represents every $c \in F$ over $K$ (via
$\langle\beta\rangle \perp \langle -c\rangle$ isotropic, `representsIn_iff_isotropicIn_orthSum`). -/
theorem represents_of_isotropic {K : Type*} [Field K] [Algebra F K] [CharZero F] {n : ℕ} (β : Fin n → F)
    (hβ : ∀ i, β i ≠ 0) (hiso : (QuadForm.diag β).IsotropicIn K) (c : F) :
    (QuadForm.diag β).RepresentsIn K c := by
  refine (QuadForm.representsIn_iff_isotropicIn_orthSum K (QuadForm.nondegenerate_diag hβ) c).2 ?_
  obtain ⟨x, hx0, hx⟩ := hiso
  refine ⟨Fin.append x 0, fun h => hx0 ?_, ?_⟩
  · funext i
    have := congrFun h (Fin.castAdd 1 i)
    simpa [Fin.append_left] using this
  · rw [QuadForm.evalIn_orthSum]
    simp [Fin.append_left, hx, QuadForm.evalIn_diag, Fin.append_right]

/-- **Odd total order gives universality on units:** if $\beta_0,\beta_1,\beta_2 \in F^\times$ have
$\operatorname{ord}_v(\beta_0)+\operatorname{ord}_v(\beta_1)+\operatorname{ord}_v(\beta_2)$ odd, then
$\langle\beta_0,\beta_1,\beta_2\rangle$ represents every $v$-unit $a$ over $F_v$. The form
$\langle\beta_0,\beta_1,\beta_2,-a\rangle$ has determinant of odd order, hence non-square, hence is isotropic;
a zero with last coordinate non-zero gives the representation, otherwise the ternary form is isotropic and universal. -/
theorem represents_unit_of_odd (β : Fin 3 → F) (hβ : ∀ i, β i ≠ 0)
    (hodd : ¬ Even (ordv v (β 0) + ordv v (β 1) + ordv v (β 2))) {a : F} (ha : v.valuation F a = 1) :
    (QuadForm.diag β).RepresentsIn Kv a := by
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  have hb : ∀ i, (![algebraMap F Kv (β 0), algebraMap F Kv (β 1), algebraMap F Kv (β 2),
      -algebraMap F Kv a] : Fin 4 → Kv) i ≠ 0 := by
    intro i
    have h := fun j => (map_ne_zero_iff _ (algebraMap F Kv).injective).2 (hβ j)
    have h' := (map_ne_zero_iff _ (algebraMap F Kv).injective).2 ha0
    fin_cases i <;> simp [h, h']
  have hns : ¬ IsSquare ((![algebraMap F Kv (β 0), algebraMap F Kv (β 1), algebraMap F Kv (β 2),
      -algebraMap F Kv a] : Fin 4 → Kv) 0 * (![algebraMap F Kv (β 0), algebraMap F Kv (β 1),
      algebraMap F Kv (β 2), -algebraMap F Kv a] : Fin 4 → Kv) 1 * (![algebraMap F Kv (β 0),
      algebraMap F Kv (β 1), algebraMap F Kv (β 2), -algebraMap F Kv a] : Fin 4 → Kv) 2 *
      (![algebraMap F Kv (β 0), algebraMap F Kv (β 1), algebraMap F Kv (β 2), -algebraMap F Kv a] :
        Fin 4 → Kv) 3) := by
    have e : algebraMap F Kv (β 0 * β 1 * β 2 * (-a)) = (![algebraMap F Kv (β 0), algebraMap F Kv (β 1),
        algebraMap F Kv (β 2), -algebraMap F Kv a] : Fin 4 → Kv) 0 * (![algebraMap F Kv (β 0),
        algebraMap F Kv (β 1), algebraMap F Kv (β 2), -algebraMap F Kv a] : Fin 4 → Kv) 1 *
        (![algebraMap F Kv (β 0), algebraMap F Kv (β 1), algebraMap F Kv (β 2), -algebraMap F Kv a] :
        Fin 4 → Kv) 2 * (![algebraMap F Kv (β 0), algebraMap F Kv (β 1), algebraMap F Kv (β 2),
        -algebraMap F Kv a] : Fin 4 → Kv) 3 := by
      simp
    rw [← e]
    refine not_isSquare_of_odd v (mul_ne_zero (mul_ne_zero (mul_ne_zero (hβ 0) (hβ 1)) (hβ 2))
      (neg_ne_zero.2 ha0)) ?_
    rw [ordv_mul v (mul_ne_zero (mul_ne_zero (hβ 0) (hβ 1)) (hβ 2)) (neg_ne_zero.2 ha0),
      ordv_mul v (mul_ne_zero (hβ 0) (hβ 1)) (hβ 2), ordv_mul v (hβ 0) (hβ 1), ordv_neg_of_unit v ha]
    simpa using hodd
  obtain ⟨z, hz0, hz⟩ := LocalRankFive.isotropic_four_of_not_isSquare v _ hb hns
  rw [LocalRankFive.evalIn_diag_four] at hz
  replace hz : algebraMap F Kv (β 0) * z 0 ^ 2 + algebraMap F Kv (β 1) * z 1 ^ 2 +
      algebraMap F Kv (β 2) * z 2 ^ 2 + (-algebraMap F Kv a) * z 3 ^ 2 = 0 := hz
  by_cases h3 : z 3 = 0
  · -- the ternary form is isotropic
    have hiso : (QuadForm.diag β).IsotropicIn Kv := by
      refine ⟨![z 0, z 1, z 2], fun h => hz0 ?_, ?_⟩
      · funext i
        fin_cases i
        · simpa using congrFun h 0
        · simpa using congrFun h 1
        · simpa using congrFun h 2
        · simpa using h3
      · rw [QuadForm.evalIn_diag, Fin.sum_univ_three]
        rw [h3] at hz
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val,
          Matrix.head_cons, Matrix.tail_cons]
        linear_combination hz
    exact represents_of_isotropic β hβ hiso a
  · refine ⟨(z 3)⁻¹ • ![z 0, z 1, z 2], ?_⟩
    rw [QuadForm.evalIn_smul, QuadForm.evalIn_diag, Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val,
      Matrix.head_cons, Matrix.tail_cons]
    field_simp
    linear_combination hz

/-- **Even orders give universality:** if $\beta_0,\beta_1,\beta_2 \in F^\times$ all have even order at $v$,
$v \nmid 2$, then $\langle\beta_0,\beta_1,\beta_2\rangle$ is isotropic over $F_v$ (it is $\langle u_0,u_1,u_2\rangle$
up to squares with $u_i$ units, `NFLocal.isotropic_diag_units_nf`), hence represents every $c \in F$. -/
theorem represents_of_even (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (β : Fin 3 → F) (hβ : ∀ i, β i ≠ 0)
    (heven : ∀ i, Even (ordv v (β i))) (c : F) : (QuadForm.diag β).RepresentsIn Kv c := by
  have ht : ∀ i, ∃ t : F, t ≠ 0 ∧ v.valuation F (β i / t ^ 2) = 1 := by
    intro i
    obtain ⟨r, hr⟩ := heven i
    have hv : v.valuation F (β i) = exp (r + r) := by
      have hne : v.valuation F (β i) ≠ 0 := (Valuation.ne_zero_iff _).mpr (hβ i)
      have := WithZero.exp_log (M := ℤ) hne
      rw [← this]; rw [hr]
    refine ⟨unifF v ^ (-r), zpow_ne_zero _ (unifF_ne_zero v), ?_⟩
    have h1 : v.valuation F (unifF v ^ (-r)) = exp r := by
      rw [map_zpow₀, valuation_unifF, ← WithZero.exp_zsmul]
      congr 1; simp
    rw [map_div₀, map_pow, h1, hv, exp_add, sq]
    exact div_self (mul_ne_zero WithZero.exp_ne_zero WithZero.exp_ne_zero)
  choose t ht0 ht using ht
  obtain ⟨z, hz0, hz⟩ := NFLocal.isotropic_diag_units_nf v h2 3 le_rfl (fun i => β i / t i ^ 2) ht
  have ht' : ∀ i, algebraMap F Kv (t i) ≠ 0 := fun i =>
    (map_ne_zero_iff _ (algebraMap F Kv).injective).2 (ht0 i)
  refine represents_of_isotropic β hβ ⟨fun i => z i / algebraMap F Kv (t i), fun h => hz0 ?_, ?_⟩ c
  · funext i
    have := congrFun h i
    simpa [ht' i] using this
  · rw [QuadForm.evalIn_diag] at hz ⊢
    rw [← hz]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := ht' i
    have h0 := ht0 i
    simp only [map_div₀, map_pow]
    field_simp

end Local

/-! ### The main statement -/

section Main

/-- A ternary regular subspace on three coordinates of odd total order. -/
theorem regTernary_of_odd (v : HeightOneSpectrum (𝓞 F)) {m : ℕ} (α : Fin m → F) (hα : ∀ i, α i ≠ 0)
    (X : Finset F) (hX : ∀ a ∈ X, a ≠ 0 → v.valuation F a = 1) (f : Fin 3 → Fin m)
    (hf : Function.Injective f)
    (hodd : ¬ Even (ordv v (α (f 0)) + ordv v (α (f 1)) + ordv v (α (f 2)))) :
    RegTernaryRepresents (QuadForm.diag α) (v.adicCompletion F) X := by
  refine regTernaryRepresents_of_coordinates α hα X f hf fun a ha => ?_
  by_cases ha0 : a = 0
  · subst ha0
    exact ⟨0, by simp [QuadForm.evalIn_diag]⟩
  · exact represents_unit_of_odd v (α ∘ f) (fun i => hα _) hodd (hX a ha ha0)

/-- A ternary regular subspace on three coordinates all of even order (at a non-dyadic spot). -/
theorem regTernary_of_even (v : HeightOneSpectrum (𝓞 F)) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) {m : ℕ}
    (α : Fin m → F) (hα : ∀ i, α i ≠ 0)
    (X : Finset F) (f : Fin 3 → Fin m) (hf : Function.Injective f) (heven : ∀ k, Even (ordv v (α (f k)))) :
    RegTernaryRepresents (QuadForm.diag α) (v.adicCompletion F) X :=
  regTernaryRepresents_of_coordinates α hα X f hf fun a _ =>
    represents_of_even v h2 (α ∘ f) (fun _ => hα _) heven a

/-- **Lemma 101:11, step 2** (O'Meara, §101C, p. 294). At a non-dyadic spot $v$, a diagonal space
$\langle \alpha_0, \dots, \alpha_{m-1}\rangle$ ($m \ge 4$, all $\alpha_i \in F^\times$) over $F_v$ has a regular ternary
subspace representing every element of a finite set $X \subseteq F$ whose non-zero elements are $v$-units. -/
@[kb "omeara1963" "§101C, proof of 101:11, step 2, p. 294 (a regular space of dimension ≥ 4 at a non-dyadic spot has a regular ternary subspace representing all units)"]
theorem regTernaryRepresents_units_nondyadic (v : HeightOneSpectrum (𝓞 F)) (h2 : (2 : 𝓞 F) ∉ v.asIdeal)
    {m : ℕ} (hm : 4 ≤ m) (α : Fin m → F) (hα : ∀ i, α i ≠ 0) (X : Finset F)
    (hX : ∀ a ∈ X, a ≠ 0 → v.valuation F a = 1) :
    RegTernaryRepresents (QuadForm.diag α) (v.adicCompletion F) X := by
  set ι : Fin 4 → Fin m := fun i => Fin.castLE hm i with hι
  have hιi : Function.Injective ι := Fin.castLE_injective hm
  set o : Fin 4 → ℤ := fun i => ordv v (α (ι i)) with ho
  have key : ∀ g : Fin 3 → Fin 4, Function.Injective g →
      ¬ Even (o (g 0) + o (g 1) + o (g 2)) →
      RegTernaryRepresents (QuadForm.diag α) (v.adicCompletion F) X := fun g hg h =>
    regTernary_of_odd v α hα X hX (ι ∘ g) (hιi.comp hg) h
  by_cases h012 : Even (o 0 + o 1 + o 2)
  · by_cases h013 : Even (o 0 + o 1 + o 3)
    · by_cases h023 : Even (o 0 + o 2 + o 3)
      · by_cases h123 : Even (o 1 + o 2 + o 3)
        · refine regTernary_of_even v h2 α hα X (ι ∘ ![0, 1, 2]) (hιi.comp (by decide)) fun k => ?_
          rw [Int.even_add, Int.even_add] at h012 h013 h023 h123
          fin_cases k
          · show Even (o 0)
            tauto
          · show Even (o 1)
            tauto
          · show Even (o 2)
            tauto
        · exact key ![1, 2, 3] (by decide) h123
      · exact key ![0, 2, 3] (by decide) h023
    · exact key ![0, 1, 3] (by decide) h013
  · exact key ![0, 1, 2] (by decide) h012

end Main
