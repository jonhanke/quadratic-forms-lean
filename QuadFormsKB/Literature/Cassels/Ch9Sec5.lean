/-
# Cassels, Chapter 9, §5: representations by the forms of a genus

**Layer:** integer-valued forms `f : QuadForm ℤ n` with $\det H \ne 0$ ($H$ the Hessian; Cassels' integral forms are
the classically integral ones, `IsClassicallyIntegral`, with $d = d(f) = \det(f_{ij}) = \det H / 2^n$); the genus
`Siegel.SameGenus` (equivalence over every $\mathbb Z_p$ = `ℤ_[p]` and over $\mathbb R$); representations over
$\mathbb Z_p$ by vectors of `Fin n → ℤ_[p]`, *primitive* when some coordinate is a unit; over $\mathbb Z$ by vectors of
`Fin n → ℤ`, *primitive* when the coordinates have greatest common divisor $1$ (Cassels' footnote, p. 130).

**Proves**
* Theorem 1.3 (`exists_sameGenus_represents`): an integer $a \ne 0$ represented by $f$ over every $\mathbb Z_p$ and
  over $\mathbb R$ is represented over $\mathbb Z$ by some form of the genus of $f$;
* Theorem 5.1 (`exists_sameGenus_primRep`): the primitive version, with the local condition only at the primes
  $p \mid 2d$ (and $p \mid 2ad$ if $n = 2$), stated as $p = 2$ or $p \mid \det H$ (or $n = 2$ and $p \mid a$);
* the Corollary to Theorem 5.1 (`exists_primRep_of_one_class`): if the genus of $f$ has one class, $f$ itself
  represents $a$ primitively.

*Generalization:* $f$ is only required to be integer-valued. For classically integral $f$, $p \mid 2d$ iff $p = 2$ or
$p \mid \det H$ ($\det H = 2^nd$).

*Proof:* the lattice forms (`Lattices.exists_sameGenus_mem`, `Lattices.exists_sameGenus_primitive`, adelic, not
Cassels' induction), transported to forms over $\mathbb Z$ by the bridges below; at the primes $p \nmid 2\det H$ the
local primitive representations exist automatically (a unimodular form over $\mathbb Z_p$, $p$ odd, in $n \ge 3$
variables represents every $p$-adic integer primitively; in $n = 2$ variables it represents every unit).
-/
import QuadFormsKB.Literature.Cassels.Ch9Sec5Lat
import QuadFormsKB.Literature.Cassels.Ch11Sec8Cor
import QuadFormsKB.Literature.Cassels.Ch11Sec6Genus
import QuadFormsKB.Lattices.SALocalRep
import QuadFormsKB.Tamagawa.RatBridge

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

variable {n : ℕ}

/-! ### Bridges between $\mathbb Z_p$ and the completion $\mathfrak o_v$ of $\mathcal O_{\mathbb Q}$ -/

/-- Evaluation of the rational form over a `ℚ`-algebra field is evaluation of the base change of the integral
form. -/
theorem evalIn_castHom_rat (f : QuadForm ℤ n) {K : Type*} [Field K] [Algebra ℚ K] (y : Fin n → K) :
    (f.map (Int.castRingHom ℚ)).evalIn K y = (f.map (Int.castRingHom K)).eval y := by
  simp [QuadForm.evalIn, QuadForm.map]

/-- A ring homomorphism commutes with evaluation of the base change of an integral form. -/
theorem hom_eval_castHom (f : QuadForm ℤ n) {A B : Type*} [CommRing A] [CommRing B] (ψ : A →+* B)
    (x : Fin n → A) :
    ψ ((f.map (Int.castRingHom A)).eval x) = (f.map (Int.castRingHom B)).eval (fun i => ψ (x i)) := by
  simp [QuadForm.evalIn, QuadForm.map, map_sum, apply_ite]

/-- A ring isomorphism `ℤ_[p] ≃ 𝔬_v` for `v` over `p`. -/
theorem exists_ringEquiv_padic (v : HeightOneSpectrum (𝓞 ℚ)) (p : ℕ) [Fact p.Prime]
    (hp : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = p) :
    Nonempty (ℤ_[p] ≃+* v.adicCompletionIntegers ℚ) := by
  subst hp
  exact ⟨(Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).symm.toAlgEquiv.toRingEquiv⟩

/-- **A representation over $\mathbb Z_p$ gives a representation by the localization $(\mathbb Z^n)_v$** at the place $v$
over $p$. -/
theorem exists_mem_std_of_padic (f : QuadForm ℤ n) (v : HeightOneSpectrum (𝓞 ℚ)) (p : ℕ) [Fact p.Prime]
    (hp : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = p) {a : ℤ}
    (h : ∃ x : Fin n → ℤ_[p], (f.map (Int.castRingHom ℤ_[p])).eval x = a) :
    ∃ y ∈ std v, (f.map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) y =
      algebraMap ℚ (v.adicCompletion ℚ) a := by
  obtain ⟨φ⟩ := exists_ringEquiv_padic v p hp
  obtain ⟨x, hx⟩ := h
  refine ⟨fun i => ((φ (x i) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ), ?_, ?_⟩
  · intro i
    simpa using (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (φ (x i)).2
  · rw [evalIn_castHom_rat]
    have := hom_eval_castHom f ((v.adicCompletionIntegers ℚ).subtype.comp (φ : ℤ_[p] →+* _)) x
    rw [hx] at this
    simpa using this.symm

/-- **A primitive representation over $\mathbb Z_p$ gives a primitive vector of $(\mathbb Z^n)_v$** representing $a$. -/
theorem exists_locPrimitive_std_of_padic (f : QuadForm ℤ n) (v : HeightOneSpectrum (𝓞 ℚ)) (p : ℕ) [Fact p.Prime]
    (hp : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = p) {a : ℤ}
    (h : ∃ x : Fin n → ℤ_[p], (∃ i, IsUnit (x i)) ∧ (f.map (Int.castRingHom ℤ_[p])).eval x = a) :
    ∃ y, LocPrimitive v (std v) y ∧ (f.map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) y =
      algebraMap ℚ (v.adicCompletion ℚ) a := by
  obtain ⟨φ⟩ := exists_ringEquiv_padic v p hp
  obtain ⟨x, ⟨i, hi⟩, hx⟩ := h
  have := hom_eval_castHom f ((v.adicCompletionIntegers ℚ).subtype.comp (φ : ℤ_[p] →+* _)) x
  refine ⟨fun i => ((φ (x i) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ), ⟨?_, ?_⟩, ?_⟩
  · intro i
    simpa using (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (φ (x i)).2
  · intro t ht
    have h1 : Valued.v (t * ((φ (x i) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ)) ≤ 1 := by
      simpa using ht i
    obtain ⟨u, hu⟩ : IsUnit (φ (x i)) := hi.map φ
    have hu1 : Valued.v (((u : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ)) = 1 := by
      have a1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (u : v.adicCompletionIntegers ℚ).2
      have a2 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (↑u⁻¹ : v.adicCompletionIntegers ℚ).2
      have a3 : Valued.v (((u : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ)) *
          Valued.v (((↑u⁻¹ : v.adicCompletionIntegers ℚ)) : v.adicCompletion ℚ) = 1 := by
        rw [← map_mul]
        have : (((u : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ)) *
          (((↑u⁻¹ : v.adicCompletionIntegers ℚ)) : v.adicCompletion ℚ) = 1 := by
          rw [← Subring.coe_mul]; simp
        rw [this, map_one]
      exact le_antisymm a1 (by
        have := mul_le_of_le_one_right' (a := Valued.v (((u : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ))) a2
        rw [a3] at this
        exact this)
    rw [← hu] at h1
    rw [map_mul, hu1, mul_one] at h1
    exact h1
  · rw [evalIn_castHom_rat]
    rw [hx] at this
    simpa using this.symm

/-- **A real representation gives a representation over the completion at the infinite place of $\mathbb Q$.** -/
theorem representsIn_inf_of_real (f : QuadForm ℤ n) {a : ℤ} (h : ∃ x : Fin n → ℝ, f.evalIn ℝ x = a) :
    ∀ w : InfinitePlace ℚ, (f.map (Int.castRingHom ℚ)).RepresentsIn w.Completion (a : ℚ) := by
  intro w
  obtain ⟨x, hx⟩ := h
  let ψ := InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)
  refine ⟨fun i => ψ.symm (x i), ?_⟩
  rw [evalIn_castHom_rat]
  have := hom_eval_castHom f ψ.symm.toRingHom x
  have e : (f.map (Int.castRingHom ℝ)).eval x = f.evalIn ℝ x := by
    simp [QuadForm.evalIn, QuadForm.map]
  rw [e, hx] at this
  simpa using this.symm

/-- Representability over a field does not depend on the choice of the (unique) `ℚ`-algebra structure. -/
theorem representsIn_congr_alg {K : Type*} [Field K] (i1 i2 : Algebra ℚ K) (Q : QuadForm ℚ n) (c : ℚ) :
    @QuadForm.RepresentsIn ℚ _ n K _ i1 Q c → @QuadForm.RepresentsIn ℚ _ n K _ i2 Q c := by
  have : i1 = i2 := Subsingleton.elim _ _
  subst this
  exact id

section Bridge

open QuadFormsKB.Tamagawa.RatBridge QuadFormsKB.HilbertModular

/-- The integer `eZ w` of `w : 𝓞 ℚ`, cast to `ℚ`, is `w`. -/
theorem eZ_cast_eq (w : 𝓞 ℚ) : ((eZ w : ℤ) : ℚ) = algebraMap (𝓞 ℚ) ℚ w := by
  conv_rhs => rw [← eZ.symm_apply_apply w, eZ_symm_apply]
  simp

/-- If every `z i` is divisible by an integer `m > 0` and `z' = eZ.symm ∘ z`, then `(1/m) • γ(z')` lies
in the lattice `latOf γ`. -/
theorem smul_mem_latOf_of_dvd (γ : GL (Fin n) ℚ) (z : Fin n → ℤ) (m : ℕ) (hm0 : 0 < m)
    (hm : ∀ i, (m : ℤ) ∣ z i) :
    ((1 : ℚ) / m) • (γ.val *ᵥ intCoe (fun i => eZ.symm (z i))) ∈ latOf γ := by
  choose w hw using hm
  refine ⟨intCoe (fun i => eZ.symm (w i)), intCoe_mem _, ?_⟩
  rw [← mulVec_smul]
  show γ.val *ᵥ _ = _
  congr 1
  funext i
  have h1 : (z i : ℚ) = m * w i := by exact_mod_cast hw i
  simp only [Pi.smul_apply, intCoe, eZ_symm_apply, map_intCast, smul_eq_mul]
  rw [h1]
  have : (m : ℚ) ≠ 0 := by exact_mod_cast hm0.ne'
  field_simp

/-- Bridge from a lattice in the genus of `ℤⁿ` to a form in the genus of `f` (proof of
`exists_sameGenus_form_of_lat`). -/
theorem exists_sameGenus_form_of_lat_aux (f : QuadForm ℤ n) (M : Lat ℚ n)
    (hM : SameGenus (f.map (Int.castRingHom ℚ)) (stdLat : Lat ℚ n).1 M.1) {x : Fin n → ℚ} (hx : x ∈ M.1) :
    ∃ f' : QuadForm ℤ n, Siegel.SameGenus f f' ∧ ∃ z : Fin n → ℤ,
      ((f'.eval z : ℤ) : ℚ) = (f.map (Int.castRingHom ℚ)).evalIn ℚ x ∧
      (LatPrimitive M.1 x → Finset.univ.gcd z = 1) := by
  have hM' : Lattices.SameGenus (formF (up f)) intVec M.1 := by rw [formF_up]; exact hM
  obtain ⟨γ, hγ, hi⟩ := exists_free_of_sameGenus f M hM'
  have hs : Lattices.SameGenus (formF (up f)) intVec (latOf γ) := hγ ▸ hM'
  refine ⟨_, sameGenus_down_gramZ f γ hs hi, ?_⟩
  have hxγ : x ∈ latOf γ := hγ ▸ hx
  obtain ⟨y, hy, rfl⟩ := hxγ
  obtain ⟨z', rfl⟩ := mem_intVec_iff_exists.mp hy
  refine ⟨fun i => eZ (z' i), ?_, ?_⟩
  · rw [down_map_eval, eZ_cast_eq, algebraMap_eval_gramZ, formF_up]
    rfl
  · intro hp
    by_contra hne
    obtain ⟨m, hm2, hm⟩ : ∃ m : ℕ, 2 ≤ m ∧ ∀ i, (m : ℤ) ∣ eZ (z' i) := by
      by_cases h0 : Finset.univ.gcd (fun i => eZ (z' i)) = 0
      · refine ⟨2, le_refl _, fun i => ?_⟩
        have := Finset.gcd_dvd (s := Finset.univ) (f := fun i => eZ (z' i)) (Finset.mem_univ i)
        rw [h0, zero_dvd_iff] at this
        rw [this]; exact dvd_zero _
      · refine ⟨(Finset.univ.gcd (fun i => eZ (z' i))).natAbs, ?_, fun i => ?_⟩
        · have h1 : (Finset.univ.gcd (fun i => eZ (z' i))).natAbs ≠ 1 := by
            intro h
            apply hne
            rcases Int.natAbs_eq_iff.mp h with h | h
            · simpa using h
            · have : 0 ≤ Finset.univ.gcd (fun i => eZ (z' i)) :=
                Int.nonneg_of_normalize_eq_self (Finset.normalize_gcd)
              omega
          have h2 : (Finset.univ.gcd (fun i => eZ (z' i))).natAbs ≠ 0 := by
            simpa using h0
          omega
        · exact Int.natAbs_dvd.mpr (Finset.gcd_dvd (Finset.mem_univ i))
    have hz := smul_mem_latOf_of_dvd γ (fun i => eZ (z' i)) m (by omega) hm
    simp only [RingEquiv.symm_apply_apply] at hz
    obtain ⟨k, hk⟩ := hp.2 ((1 : ℚ) / m) (hγ ▸ hz)
    have h3 : ((eZ k * m : ℤ) : ℚ) = 1 := by
      push_cast
      rw [eZ_cast_eq, hk]
      have : (m : ℚ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
      field_simp
    have h4 : (m : ℤ) ∣ 1 := ⟨eZ k, by
      have : eZ k * (m : ℤ) = 1 := by exact_mod_cast h3
      linarith⟩
    have h5 := Int.eq_one_of_dvd_one (by positivity) h4
    omega

end Bridge

/-- **From a lattice of the genus of $\mathbb Z^n$ back to a form of the genus of $f$:** if $M$ is in the genus of
$\mathbb Z^n$ in $(\mathbb Q^n, f)$ and $x \in M$, there is a form $f'$ in the genus of $f$ and $z \in \mathbb Z^n$ with
$f'(z) = f(x)$; if $x$ is primitive in $M$, $z$ is primitive. -/
theorem exists_sameGenus_form_of_lat (f : QuadForm ℤ n) (M : Lat ℚ n)
    (hM : SameGenus (f.map (Int.castRingHom ℚ)) (stdLat : Lat ℚ n).1 M.1) {x : Fin n → ℚ} (hx : x ∈ M.1) :
    ∃ f' : QuadForm ℤ n, Siegel.SameGenus f f' ∧ ∃ z : Fin n → ℤ,
      ((f'.eval z : ℤ) : ℚ) = (f.map (Int.castRingHom ℚ)).evalIn ℚ x ∧
      (LatPrimitive M.1 x → Finset.univ.gcd z = 1) := by
  exact exists_sameGenus_form_of_lat_aux f M hM hx

/-! ### Automatic local primitive representations -/

section PrimDVR

open QuadFormsKB.LocalDensity QuadFormsKB.Siegel.Kneser

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Fintype (IsLocalRing.ResidueField R)] [DecidableEq (IsLocalRing.ResidueField R)]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

/-- A vector with all coordinates non-units has non-unit value. -/
theorem eval_not_isUnit_of_forall {m : ℕ} (Q : QuadForm R m) (x : Fin m → R)
    (hx : ∀ i, ¬ IsUnit (x i)) : ¬ IsUnit (Q.eval x) := by
  have h : Q.eval x ∈ IsLocalRing.maximalIdeal R := by
    unfold QuadForm.eval QuadForm.evalIn
    refine Ideal.sum_mem _ fun i _ => Ideal.sum_mem _ fun j _ => ?_
    split_ifs
    · simp only [Algebra.algebraMap_self, RingHom.id_apply]
      exact Ideal.mul_mem_left _ _ (hx j)
    · exact Ideal.zero_mem _
  exact h

/-- **A unimodular form in $m \ge 3$ variables over a complete non-dyadic DVR represents every element
primitively** (some coordinate is a unit): the proof of `LocRep.exists_eval_eq_dvr` with `x = U z`, `z i₂ = 1`. -/
theorem exists_primitive_eval_dvr {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2) {m : ℕ} (Q₀ : QuadForm R m)
    (hdet : ¬ π ∣ Q₀.hessian.det) (hm : 3 ≤ m) (c : R) :
    ∃ x : Fin m → R, (∃ i, IsUnit (x i)) ∧ Q₀.eval x = c := by
  by_cases hc : IsUnit c
  · obtain ⟨x, hx⟩ := exists_eval_eq_unit_dvr hπ h2 Q₀ hdet (by omega) hc
    refine ⟨x, ?_, hx⟩
    by_contra h
    push Not at h
    exact eval_not_isUnit_of_forall Q₀ x h (hx ▸ hc)
  obtain ⟨a, ha, ⟨U, hUd, hU⟩, -⟩ := DVR.exists_diag_of_unimodular Q₀ π hπ h2 hdet
  have haU : ∀ i, IsUnit (a i) := fun i => DVR.isUnit_of_not_dvd _ hπ _ (ha i)
  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  let i2 : Fin m := ⟨2, by omega⟩
  have hcm : c ∈ IsLocalRing.maximalIdeal R := hc
  have hd : IsUnit (c - a i2) := by
    by_contra h
    have h' : c - a i2 ∈ IsLocalRing.maximalIdeal R := h
    have : a i2 ∈ IsLocalRing.maximalIdeal R := by
      have := Ideal.sub_mem _ hcm h'; simpa using this
    exact this (haU i2)
  obtain ⟨s, t, hst⟩ := Nbr.exists_binary_one_dvr hπ h2 ((haU i0).mul hd.unit⁻¹.isUnit)
    ((haU i1).mul hd.unit⁻¹.isUnit)
  let z : Fin m → R := Pi.single i0 s + Pi.single i1 t + Pi.single i2 1
  refine ⟨U *ᵥ z, ?_, ?_⟩
  · by_contra h
    push Not at h
    have hz2 : z i2 = 1 := by
      have h02 : i2 ≠ i0 := by simp [i0, i2, Fin.ext_iff]
      have h12 : i2 ≠ i1 := by simp [i1, i2, Fin.ext_iff]
      simp [z, h02, h12]
    have e : z = U⁻¹ *ᵥ (U *ᵥ z) := by
      rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ hUd, one_mulVec]
    have : z i2 ∈ IsLocalRing.maximalIdeal R := by
      rw [e]
      simp only [mulVec, dotProduct]
      exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (h j)
    rw [hz2] at this
    exact this isUnit_one
  rw [← hU, eval_diag]
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
  have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  have hz : ∀ i, a i * z i ^ 2 = (if i = i0 then a i0 * s ^ 2 else 0) + (if i = i1 then a i1 * t ^ 2 else 0) +
      (if i = i2 then a i2 else 0) := by
    intro i
    by_cases e0 : i = i0
    · subst e0; simp [z, h01, h02]
    · by_cases e1 : i = i1
      · subst e1; simp [z, e0, h12]
      · by_cases e2 : i = i2
        · subst e2; simp [z, e0, e1]
        · simp [z, e0, e1, e2]
  rw [Finset.sum_congr rfl fun i _ => hz i, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  have hinv : (↑hd.unit⁻¹ : R) * (c - a i2) = 1 := hd.val_inv_mul
  have := congrArg (· * (c - a i2)) hst
  simp only [one_mul] at this
  linear_combination this - (a i0 * s ^ 2 + a i1 * t ^ 2) * hinv

end PrimDVR

section PrimPadic

open QuadFormsKB.LocalDensity

/-- If `p ∤ det H` in `ℤ`, then `p ∤ det H` of the base change to `ℤ_[p]`. -/
theorem padic_not_dvd_det (p : ℕ) [Fact p.Prime] (f : QuadForm ℤ n) (hdet : ¬ (p : ℤ) ∣ f.hessian.det) :
    ¬ (p : ℤ_[p]) ∣ (f.map (Int.castRingHom ℤ_[p])).hessian.det := by
  rw [det_map_padic]
  intro h
  exact hdet (by simpa using (padic_pow_dvd_int_iff p 1 _).1 (by simpa using h))

/-- For odd `p`, `p ∤ 2` in `ℤ_[p]`. -/
theorem padic_not_dvd_two (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) : ¬ (p : ℤ_[p]) ∣ 2 := by
  have := (padicInt_pow_dvd_two p).2
  simpa [hp2] using this

end PrimPadic

/-- **A unimodular form over $\mathbb Z_p$ ($p$ odd) in $n \ge 3$ variables represents every $p$-adic integer
primitively** (O'Meara 92:1b; the proof of `LocRep.exists_eval_eq_dvr` gives a primitive vector). -/
theorem exists_primitive_padic_of_unimodular (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (f : QuadForm ℤ n)
    (hdet : ¬ (p : ℤ) ∣ f.hessian.det) (hn : 3 ≤ n) (a : ℤ) :
    ∃ x : Fin n → ℤ_[p], (∃ i, IsUnit (x i)) ∧ (f.map (Int.castRingHom ℤ_[p])).eval x = a := by
  classical
  let _ : Fintype (IsLocalRing.ResidueField ℤ_[p]) := Fintype.ofFinite _
  exact exists_primitive_eval_dvr PadicInt.irreducible_p (padic_not_dvd_two p hp2) _
    (padic_not_dvd_det p f hdet) hn (a : ℤ_[p])

/-- **A unimodular binary form over $\mathbb Z_p$ ($p$ odd) represents every unit primitively.** -/
theorem exists_primitive_padic_of_unimodular_two (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (f : QuadForm ℤ 2)
    (hdet : ¬ (p : ℤ) ∣ f.hessian.det) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    ∃ x : Fin 2 → ℤ_[p], (∃ i, IsUnit (x i)) ∧ (f.map (Int.castRingHom ℤ_[p])).eval x = a := by
  classical
  let _ : Fintype (IsLocalRing.ResidueField ℤ_[p]) := Fintype.ofFinite _
  have hu : IsUnit (a : ℤ_[p]) := by
    apply LocalDensity.DVR.isUnit_of_not_dvd _ PadicInt.irreducible_p
    intro h
    exact ha (by simpa using (LocalDensity.padic_pow_dvd_int_iff p 1 _).1 (by simpa using h))
  obtain ⟨x, hx⟩ := exists_eval_eq_unit_dvr PadicInt.irreducible_p (padic_not_dvd_two p hp2) _
    (padic_not_dvd_det p f hdet) (le_refl 2) hu
  refine ⟨x, ?_, hx⟩
  by_contra h
  push Not at h
  exact eval_not_isUnit_of_forall _ x h (hx ▸ hu)

end QuadFormsKB.Lattices

namespace QuadFormsKB.Siegel

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

variable {n : ℕ}

/-- **Cassels, Theorem 1.3** (Ch. 9, p. 129): *let $f(\mathbf x)$ be a regular integral form and let $a \ne 0$ be an
integer which is represented by $f$ over each $\mathbb Z_p$ (including $p = \infty$). Then $a$ is represented over
$\mathbb Z$ by some form $f^{*}$ in the same genus as $f$.* (Here $f$ is integer-valued; module docstring.) -/
@[kb "cassels1978" "Ch. 9, Thm. 1.3, p. 129"]
theorem exists_sameGenus_represents (f : QuadForm ℤ n) (hf : f.hessian.det ≠ 0) {a : ℤ} (ha : a ≠ 0)
    (hreal : ∃ x : Fin n → ℝ, f.evalIn ℝ x = a)
    (hloc : ∀ (p : ℕ) [Fact p.Prime], ∃ x : Fin n → ℤ_[p], (f.map (Int.castRingHom ℤ_[p])).eval x = a) :
    ∃ f' : QuadForm ℤ n, SameGenus f f' ∧ ∃ x : Fin n → ℤ, f'.eval x = a := by
  classical
  have hQ := Lattices.nondegenerate_map_of_det_ne_zero f hf
  have haq : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have hloc' : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      ∃ y ∈ Lattices.loc v (Lattices.stdLat : Lattices.Lat ℚ n).1,
        (f.map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) y =
          algebraMap ℚ (v.adicCompletion ℚ) (a : ℚ) := by
    intro v
    obtain ⟨p, hpdef⟩ : ∃ p : ℕ, (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = p := ⟨_, rfl⟩
    have : Fact p.Prime := ⟨hpdef ▸ (Rat.HeightOneSpectrum.primesEquiv v).2⟩
    obtain ⟨y, hy, h⟩ := Lattices.exists_mem_std_of_padic f v p hpdef (hloc p)
    refine ⟨y, ?_, h⟩
    change y ∈ Lattices.loc v Lattices.intVec
    rw [Lattices.loc_intVec]
    exact hy
  have hrep : (f.map (Int.castRingHom ℚ)).RepresentsIn ℚ (a : ℚ) := by
    rw [represents_iff_everywhere_nf _ hQ _ haq]
    intro w
    cases w with
    | infinite w =>
      exact Lattices.representsIn_congr_alg _ _ _ _ (Lattices.representsIn_inf_of_real f hreal w)
    | finite v =>
      obtain ⟨y, -, hy⟩ := hloc' v
      exact ⟨y, hy⟩
  obtain ⟨x, hx⟩ := hrep
  have hx' : (f.map (Int.castRingHom ℚ)).evalIn ℚ x = a := by simpa using hx
  obtain ⟨M, hM, hxM⟩ := Lattices.exists_sameGenus_mem (f.map (Int.castRingHom ℚ)) Lattices.stdLat haq hx' hloc'
  obtain ⟨f', hg, z, hz, -⟩ := Lattices.exists_sameGenus_form_of_lat f M hM hxM
  refine ⟨f', hg, z, ?_⟩
  rw [hx'] at hz
  exact_mod_cast hz

/-- **Cassels, Theorem 5.1** (Ch. 9, p. 143): *let $f(\mathbf x)$ be an integral form in $n$ variables of determinant
$d \ne 0$. Let $a \ne 0$ be an integer which is represented by $f(\mathbf x)$ over $\mathbb R$ and primitively represented
by $f(\mathbf x)$ over $\mathbb Z_p$ for all $p \mid 2d$ (if $n \ge 3$), all $p \mid 2ad$ (if $n = 2$). Then $a$ is
primitively represented over $\mathbb Z$ by some form $f^{*}$ in the same genus as $f$.*

Here $n \ge 2$ (Cassels states no condition for $n = 1$), $f$ is integer-valued, and "$p \mid 2d$" is "$p = 2$ or
$p \mid \det H$" (module docstring). -/
@[kb "cassels1978" "Ch. 9, Thm. 5.1, p. 143"]
theorem exists_sameGenus_primRep (f : QuadForm ℤ n) (hn : 2 ≤ n) (hf : f.hessian.det ≠ 0) {a : ℤ} (ha : a ≠ 0)
    (hreal : ∃ x : Fin n → ℝ, f.evalIn ℝ x = a)
    (hloc : ∀ (p : ℕ) [Fact p.Prime], (p = 2 ∨ (p : ℤ) ∣ f.hessian.det ∨ (n = 2 ∧ (p : ℤ) ∣ a)) →
      ∃ x : Fin n → ℤ_[p], (∃ i, IsUnit (x i)) ∧ (f.map (Int.castRingHom ℤ_[p])).eval x = a) :
    ∃ f' : QuadForm ℤ n, SameGenus f f' ∧ ∃ x : Fin n → ℤ, Finset.univ.gcd x = 1 ∧ f'.eval x = a := by
  classical
  have hQ := Lattices.nondegenerate_map_of_det_ne_zero f hf
  have haq : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have hloc' : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      ∃ y, Lattices.LocPrimitive v (Lattices.loc v (Lattices.stdLat : Lattices.Lat ℚ n).1) y ∧
        (f.map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) y =
          algebraMap ℚ (v.adicCompletion ℚ) (a : ℚ) := by
    intro v
    obtain ⟨p, hpdef⟩ : ∃ p : ℕ, (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = p := ⟨_, rfl⟩
    have : Fact p.Prime := ⟨hpdef ▸ (Rat.HeightOneSpectrum.primesEquiv v).2⟩
    have key : ∃ x : Fin n → ℤ_[p], (∃ i, IsUnit (x i)) ∧
        (f.map (Int.castRingHom ℤ_[p])).eval x = a := by
      by_cases hc : p = 2 ∨ (p : ℤ) ∣ f.hessian.det ∨ (n = 2 ∧ (p : ℤ) ∣ a)
      · exact hloc p hc
      · have hp2 : p ≠ 2 := fun h => hc (Or.inl h)
        have hd : ¬ (p : ℤ) ∣ f.hessian.det := fun h => hc (Or.inr (Or.inl h))
        by_cases h3 : 3 ≤ n
        · exact Lattices.exists_primitive_padic_of_unimodular p hp2 f hd h3 a
        · have hn2 : n = 2 := by omega
          subst hn2
          exact Lattices.exists_primitive_padic_of_unimodular_two p hp2 f hd
            (fun h => hc (Or.inr (Or.inr ⟨rfl, h⟩)))
    obtain ⟨y, hy, h⟩ := Lattices.exists_locPrimitive_std_of_padic f v p hpdef key
    refine ⟨y, ?_, h⟩
    change Lattices.LocPrimitive v (Lattices.loc v Lattices.intVec) y
    rw [Lattices.loc_intVec]
    exact hy
  obtain ⟨M, hM, x, hxp, hxa⟩ := Lattices.exists_sameGenus_primitive (f.map (Int.castRingHom ℚ)) hQ
    Lattices.stdLat haq
    (fun w => Lattices.representsIn_congr_alg _ _ _ _ (Lattices.representsIn_inf_of_real f hreal w)) hloc'
  obtain ⟨f', hg, z, hz, hgcd⟩ := Lattices.exists_sameGenus_form_of_lat f M hM hxp.1
  refine ⟨f', hg, z, hgcd hxp, ?_⟩
  rw [hxa] at hz
  exact_mod_cast hz

/-- **Cassels, Theorem 5.1, Corollary** (Ch. 9, p. 143): *suppose, further, that $f$ is in a genus of one class. Then
we may suppose that $f^{*} = f$.* -/
@[kb "cassels1978" "Ch. 9, Thm. 5.1, Cor., p. 143"]
theorem exists_primRep_of_one_class (f : QuadForm ℤ n) (hn : 2 ≤ n) (hf : f.hessian.det ≠ 0)
    (hone : ∀ f', SameGenus f f' → IntEquiv f f') {a : ℤ} (ha : a ≠ 0)
    (hreal : ∃ x : Fin n → ℝ, f.evalIn ℝ x = a)
    (hloc : ∀ (p : ℕ) [Fact p.Prime], (p = 2 ∨ (p : ℤ) ∣ f.hessian.det ∨ (n = 2 ∧ (p : ℤ) ∣ a)) →
      ∃ x : Fin n → ℤ_[p], (∃ i, IsUnit (x i)) ∧ (f.map (Int.castRingHom ℤ_[p])).eval x = a) :
    ∃ x : Fin n → ℤ, Finset.univ.gcd x = 1 ∧ f.eval x = a := by
  obtain ⟨f', hg, x, hx, hev⟩ := exists_sameGenus_primRep f hn hf ha hreal hloc
  obtain ⟨g, hg'⟩ := hone f' hg
  refine ⟨g.val *ᵥ x, ?_, by rw [hg', hev]⟩
  have hdvd : Finset.univ.gcd (g.val *ᵥ x) ∣ Finset.univ.gcd x := by
    refine Finset.dvd_gcd fun i _ => ?_
    have e : x = (g⁻¹ : GL (Fin n) ℤ).val *ᵥ (g.val *ᵥ x) := by
      rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    have e' : x i = ∑ j, (g⁻¹ : GL (Fin n) ℤ).val i j * (g.val *ᵥ x) j := congrFun e i
    rw [e']
    exact Finset.dvd_sum fun j _ => Dvd.dvd.mul_left (Finset.gcd_dvd (Finset.mem_univ j)) _
  rw [hx] at hdvd
  exact Int.eq_one_of_dvd_one (Int.nonneg_of_normalize_eq_self Finset.normalize_gcd) hdvd

end QuadFormsKB.Siegel
