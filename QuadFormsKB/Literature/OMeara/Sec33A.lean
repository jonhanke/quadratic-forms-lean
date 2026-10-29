/-
# O'Meara §32A, §33B-C, §33F: normalized values, norm of an ideal, absolute units, finiteness of primes of bounded norm

**Setting.** $F$ a number field (`NumberField F`), finite spots = height-one primes of $\mathcal O_F$ with
$N\mathfrak p$ = `normPrime` = the cardinality of $\mathcal O_F/\mathfrak p$. Function fields are not covered
(O'Meara's global fields include them).

**Proves**
* 33:3 `idealNorm_eq_prod_inv_normalizedAbs`: $N\mathfrak a = \prod_{\mathfrak p} |\mathfrak a|_{\mathfrak p}^{-1}$ with
  $|\mathfrak a|_{\mathfrak p} = (N\mathfrak p)^{-\operatorname{ord}_{\mathfrak p}\mathfrak a}$, and $N\mathfrak a$ = Mathlib's `absNorm`;
* 33:6 `absoluteUnits_finite_cyclic_rootsOfUnity`: absolute units = roots of unity, a finite cyclic group
  (via Mathlib's `Units.mem_torsion`, Kronecker);
* 33:7 `finite_primes_norm_le`: finitely many primes with $N\mathfrak p \le K$.
-/
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.FractionalIdeal.Norm
import QuadFormsKB.Citation

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain WithZero
open scoped nonZeroDivisors

noncomputable section

namespace QuadFormsKB.OMeara

variable (F : Type*) [Field F] [NumberField F]

/-- The number $N\mathfrak p$ of elements of the residue class field of the number field $F$ at the finite
prime $\mathfrak p$ (O'Meara 32A: $N\mathfrak p$ is the number of elements of the residue class field). -/
def normPrime (v : HeightOneSpectrum (𝓞 F)) : ℕ := Nat.card (𝓞 F ⧸ v.asIdeal)

/-- **O'Meara 33:7.** For a positive constant $K$ there are only finitely many discrete spots $\mathfrak p$ of the
number field $F$ with $N\mathfrak p \le K$. -/
@[kb "omeara1963" "§33F, 33:7, p. 74"]
theorem finite_primes_norm_le (K : ℕ) : {v : HeightOneSpectrum (𝓞 F) | normPrime F v ≤ K}.Finite := by
  have h := Set.finite_coe_iff.mp (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) K)
  refine (h.preimage (f := HeightOneSpectrum.asIdeal) ?_).subset ?_
  · intro v _ w _ hvw
    exact HeightOneSpectrum.ext hvw
  · intro v hv
    simpa [normPrime, Ideal.absNorm_apply, Submodule.cardQuot_apply] using hv


/-- The group $\mathfrak u(\Omega)$ of **absolute units** of the number field $F$ (O'Meara 33F): the elements $a$
with $|a|_{\mathfrak p} = 1$ at every spot $\mathfrak p$ of $F$, finite (`HeightOneSpectrum`, any normalization has
the same unit locus) and infinite (`InfinitePlace`). -/
@[kb "omeara1963" "§33F, p. 73 (group of absolute units u(Ω))"]
def absoluteUnits : Subgroup Fˣ where
  carrier := {x | (∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (x : F) = 1) ∧
    ∀ w : InfinitePlace F, w (x : F) = 1}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨fun v => by simp [ha1 v, hb1 v], fun w => by simp [ha2 w, hb2 w]⟩
  one_mem' := ⟨fun v => by simp, fun w => by simp⟩
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    exact ⟨fun v => by simp [ha1 v], fun w => by simp [ha2 w]⟩

theorem valuation_eq_one_of_mul_eq_one {y z : ℤᵐ⁰} (hy : y ≤ 1) (hz : z ≤ 1) (h : y * z = 1) : y = 1 := by
  refine le_antisymm hy ?_
  calc (1 : ℤᵐ⁰) = y * z := h.symm
    _ ≤ y * 1 := mul_le_mul_right hz y
    _ = y := mul_one y

theorem mem_absoluteUnits_iff_exists (x : Fˣ) :
    x ∈ absoluteUnits F ↔ ∃ u ∈ Units.torsion F, Units.map (algebraMap (𝓞 F) F : 𝓞 F →* F) u = x := by
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F (x : F)
      (fun v : HeightOneSpectrum (𝓞 F) => (h1 v).le)
    obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F ((x⁻¹ : Fˣ) : F)
      (fun v : HeightOneSpectrum (𝓞 F) => by simp [h1 v])
    have hab : a * b = 1 := by
      apply IsFractionRing.injective (𝓞 F) F
      simp only [map_mul, map_one]
      change (algebraMap (𝓞 F) F) a * (algebraMap (𝓞 F) F) b = 1
      rw [ha, hb]; simp
    refine ⟨Units.mkOfMulEqOne a b hab, ?_, ?_⟩
    · rw [Units.mem_torsion]
      intro w
      have := h2 w
      simpa [ha] using this
    · ext; simp [ha]
  · rintro ⟨u, hu, rfl⟩
    rw [Units.mem_torsion] at hu
    refine ⟨fun v => ?_, fun w => ?_⟩
    · have h1 : v.valuation F (algebraMap (𝓞 F) F (u : 𝓞 F)) ≤ 1 := v.valuation_le_one _
      have h2 : v.valuation F (algebraMap (𝓞 F) F ((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F)) ≤ 1 := v.valuation_le_one _
      show v.valuation F (algebraMap (𝓞 F) F (u : 𝓞 F)) = 1
      refine valuation_eq_one_of_mul_eq_one h1 h2 ?_
      rw [← Valuation.map_mul, ← map_mul]
      simp
    · simpa using hu w


theorem eq_one_of_pow_eq_one_withZero (y : ℤᵐ⁰) (hy : y ≠ 0) (n : ℕ) (hn : n ≠ 0) (h : y ^ n = 1) :
    y = 1 := by
  obtain ⟨a, rfl⟩ := WithZero.ne_zero_iff_exists.1 hy
  rw [← WithZero.coe_pow, ← WithZero.coe_one, WithZero.coe_inj] at h
  have : (Multiplicative.toAdd a) * n = 0 := by
    have := congrArg Multiplicative.toAdd h
    simpa [toAdd_pow, mul_comm] using this
  have ha : Multiplicative.toAdd a = 0 := by
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd (by exact_mod_cast h) hn
  have : a = 1 := by simpa using ha
  rw [this]; rfl

/-- **O'Meara 33:6.** The group of absolute units of a number field is finite cyclic, and consists exactly of
the roots of unity in the field: $x \in F^{\times}$ has $|x|_{\mathfrak p} = 1$ at every spot if and only if $x$
has finite order. -/
@[kb "omeara1963" "§33F, 33:6, p. 73"]
theorem absoluteUnits_finite_cyclic_rootsOfUnity :
    Finite (absoluteUnits F) ∧ IsCyclic (absoluteUnits F) ∧
      ∀ x : Fˣ, x ∈ absoluteUnits F ↔ IsOfFinOrder x := by
  have hfin : Finite (absoluteUnits F) := by
    refine Finite.of_surjective (fun u : Units.torsion F =>
      (⟨Units.map (algebraMap (𝓞 F) F : 𝓞 F →* F) u.1,
        (mem_absoluteUnits_iff_exists F _).2 ⟨u.1, u.2, rfl⟩⟩ : absoluteUnits F)) ?_
    rintro ⟨x, hx⟩
    obtain ⟨u, hu, rfl⟩ := (mem_absoluteUnits_iff_exists F x).1 hx
    exact ⟨⟨u, hu⟩, rfl⟩
  refine ⟨hfin, isCyclic_subgroup_units _, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · obtain ⟨u, hu, rfl⟩ := (mem_absoluteUnits_iff_exists F x).1 hx
    exact MonoidHom.isOfFinOrder (Units.map (algebraMap (𝓞 F) F : 𝓞 F →* F)) ((CommGroup.mem_torsion _).1 hu)
  · obtain ⟨n, hn, hxn⟩ := (isOfFinOrder_iff_pow_eq_one.1 hx)
    refine ⟨fun v => ?_, fun w => ?_⟩
    · have hx0 : v.valuation F (x : F) ≠ 0 := by simp
      refine eq_one_of_pow_eq_one_withZero _ hx0 n hn.ne' ?_
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hxn]; simp
    · have h : (w (x : F)) ^ n = 1 := by
        rw [← map_pow, ← Units.val_pow_eq_pow_val, hxn]; simp
      exact (pow_eq_one_iff_of_nonneg (by positivity) hn.ne').1 h


/-- The normalized absolute value of a fractional ideal $\mathfrak a$ at the finite prime $\mathfrak p$ of the number
field $F$: $|\mathfrak a|_{\mathfrak p} = (N\mathfrak p)^{-\operatorname{ord}_{\mathfrak p}\mathfrak a}$ (O'Meara 32A, 22B). -/
@[kb "omeara1963" "§32A, p. 59 (normalized valuation on ideals)"]
def normalizedAbs (v : HeightOneSpectrum (𝓞 F)) (a : FractionalIdeal (𝓞 F)⁰ F) : ℚ :=
  (normPrime F v : ℚ) ^ (-FractionalIdeal.count F v a)

/-- **O'Meara §33C (definition of the norm).** The norm of a fractional ideal,
$N\mathfrak a = \prod_{\mathfrak p}(N\mathfrak p)^{\operatorname{ord}_{\mathfrak p}\mathfrak a}$. -/
@[kb "omeara1963" "§33C, p. 67 (norm N𝔞 of a fractional ideal)"]
def idealNorm (a : FractionalIdeal (𝓞 F)⁰ F) : ℚ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 F), (normPrime F v : ℚ) ^ FractionalIdeal.count F v a

/-- **O'Meara 33:3.** $N\mathfrak a = \prod_{\mathfrak p} 1/|\mathfrak a|_{\mathfrak p}$ with the normalized absolute
values; moreover $N\mathfrak a$ is the Mathlib norm `FractionalIdeal.absNorm`. -/
@[kb "omeara1963" "§33C, 33:3, p. 68"]
theorem idealNorm_eq_prod_inv_normalizedAbs (a : FractionalIdeal (𝓞 F)⁰ F) (ha : a ≠ 0) :
    idealNorm F a = ∏ᶠ v : HeightOneSpectrum (𝓞 F), (normalizedAbs F v a)⁻¹ ∧
      idealNorm F a = FractionalIdeal.absNorm a := by
  refine ⟨finprod_congr fun v => ?_, ?_⟩
  · simp [normalizedAbs, zpow_neg]
  · conv_rhs => rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := F) ha]
    have hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
        (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ FractionalIdeal.count F v a).Finite := by
      refine (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors a)).subset fun v hv => ?_
      intro h
      apply hv
      simp [h]
    rw [idealNorm, map_finprod (FractionalIdeal.absNorm : FractionalIdeal (𝓞 F)⁰ F →*₀ ℚ) hfin]
    refine finprod_congr fun v => ?_
    rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm, normPrime, Ideal.absNorm_apply,
      Submodule.cardQuot_apply]

end QuadFormsKB.OMeara
