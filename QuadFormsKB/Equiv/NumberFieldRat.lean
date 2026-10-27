/-
# The number-field places of $\mathbb{Q}$ versus `RatPlace`

For $F = \mathbb{Q}$, the places `NFPlace ℚ` (Mathlib's infinite place and the primes of
$\mathcal{O}_{\mathbb{Q}}$) correspond to `RatPlace` ($\infty$ and the primes $p$). The completions
correspond too: the infinite completion is $\mathbb{R}$, and the completion at the prime $(p)$ is
$\mathbb{Q}_p$ (Mathlib's `Rat.HeightOneSpectrum.padicEquiv`). This file states that local
conditions and local Hilbert symbols agree under this correspondence, and derives the
$F = \mathbb{Q}$ cases of the number-field statements from the $\mathbb{Q}$ theorems.
-/
import QuadFormsKB.Literature.LocalGlobal.NumberField
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowski

open NumberField

namespace QuadFormsKB

variable {n : ℕ}

/-- **Bridge: local isotropy everywhere, two ways.** For a rational form $Q$, "isotropic over
every completion of $\mathbb{Q}$" means the same thing whether the places are taken as number-field
places (`NFPlace ℚ`) or as `RatPlace` ($\mathbb{R}$ and the $\mathbb{Q}_p$). -/
@[kb "omeara1963" "§§11, 21 [unverified]"]
theorem everywhere_isotropic_rat_iff (Q : RatQF n) :
    NFPlace.Everywhere (F := ℚ) (fun K _ _ => Q.IsotropicIn K) ↔
      RatPlace.Everywhere (fun K _ _ => Q.IsotropicIn K) := by
  have key : ∀ (K L : Type) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] (f : K →+* L),
      Q.IsotropicIn K → Q.IsotropicIn L := by
    intro K L _ _ _ _ f hK
    obtain ⟨x, hx, h⟩ := hK
    have hf : algebraMap ℚ L = f.comp (algebraMap ℚ K) := Subsingleton.elim _ _
    refine ⟨f ∘ x, ?_, ?_⟩
    · intro h0
      apply hx
      funext i
      have := congrFun h0 i
      simpa using this
    · have : QuadForm.evalIn L Q (f ∘ x) = f (QuadForm.evalIn K Q x) := by
        simp only [QuadForm.evalIn, map_sum, hf]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> simp
      rw [this, h, map_zero]
  constructor
  · intro h v
    cases v with
    | infinite =>
      have := h (.infinite Rat.infinitePlace)
      exact key _ _ (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).toRingHom this
    | finite p =>
      obtain ⟨v, rfl⟩ := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).surjective p
      have := h (.finite v)
      exact key _ _ (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toAlgEquiv.toRingEquiv.toRingHom this
  · intro h v
    cases v with
    | infinite w =>
      have := h .infinite
      exact key _ _ (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.toRingHom this
    | finite v =>
      have := h (.finite (Rat.HeightOneSpectrum.primesEquiv v))
      exact key _ _ (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toAlgEquiv.toRingEquiv.symm.toRingHom this

/-- **Bridge: local representation everywhere, two ways** (as for isotropy). -/
@[kb "omeara1963" "§§11, 21 [unverified]"]
theorem everywhere_represents_rat_iff (Q : RatQF n) (c : ℚ) :
    NFPlace.Everywhere (F := ℚ) (fun K _ _ => Q.RepresentsIn K c) ↔
      RatPlace.Everywhere (fun K _ _ => Q.RepresentsIn K c) := by
  have tr : ∀ (K L : Type) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] (f : K →+* L),
      QuadForm.RepresentsIn K Q c → QuadForm.RepresentsIn L Q c := by
    intro K L _ _ _ _ f ⟨x, hx⟩
    have key : ∀ q, f (algebraMap ℚ K q) = algebraMap ℚ L q := fun q => by
      rw [← RingHom.comp_apply]; congr 1; exact Subsingleton.elim _ _
    refine ⟨f ∘ x, ?_⟩
    have := congrArg f hx
    simp only [QuadForm.evalIn, map_sum, apply_ite f, map_mul, key, map_zero] at this
    simpa [QuadForm.evalIn, key] using this
  constructor
  · intro h v
    cases v with
    | infinite =>
      obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace ℚ) := inferInstance
      have := h (.infinite w)
      exact tr _ _ (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).toRingHom this
    | finite p =>
      obtain ⟨v, rfl⟩ := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).surjective p
      exact tr _ _ (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv.toRingHom (h (.finite v))
  · intro h v
    cases v with
    | infinite w =>
      exact tr _ _ (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.toRingHom (h .infinite)
    | finite v =>
      exact tr _ _ (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv.symm.toRingHom (h (.finite (Rat.HeightOneSpectrum.primesEquiv v)))

/-- **Bridge: local Hilbert symbols, two ways.** For $a, b \in \mathbb{Q}^\times$, the sets of places
where $(a,b)_v = -1$ correspond: one is finite iff the other is, and they have the same size. -/
@[kb "omeara1963" "§71 [unverified]"]
theorem hilbert_minus_one_rat_iff (a b : ℚ) :
    ({v : NFPlace ℚ | v.hilbert a b = -1}.Finite ↔ {v : RatPlace | v.hilbert a b = -1}.Finite) ∧
      {v : NFPlace ℚ | v.hilbert a b = -1}.ncard = {v : RatPlace | v.hilbert a b = -1}.ncard := by
  have X : ∀ {K L : Type} [Field K] [Field L] (e : K ≃+* L) (x y : K),
      QuadFormsKB.hilbertSymbol L (e x) (e y) = QuadFormsKB.hilbertSymbol K x y := by
    intro K L _ _ e x y
    unfold QuadFormsKB.hilbertSymbol
    congr 1
    apply propext
    constructor
    · rintro ⟨a, b, c, h0, h⟩
      refine ⟨e.symm a, e.symm b, e.symm c, ?_, ?_⟩
      · intro hz
        apply h0
        simp only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] at hz ⊢
        obtain ⟨h1, h2, h3⟩ := hz
        refine ⟨?_, ?_, ?_⟩
        · simpa using congrArg e h1
        · simpa using congrArg e h2
        · simpa using congrArg e h3
      · apply e.injective
        simp [map_add, map_mul, map_pow, h]
    · rintro ⟨a, b, c, h0, h⟩
      refine ⟨e a, e b, e c, ?_, ?_⟩
      · intro hz
        apply h0
        simp only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, map_eq_zero_iff _ e.injective] at hz ⊢
        exact hz
      · rw [← map_pow, h]; simp
  let f : QuadFormsKB.NFPlace ℚ → QuadFormsKB.RatPlace := fun v => match v with
    | .infinite _ => .infinite
    | .finite v => .finite (Rat.HeightOneSpectrum.primesEquiv v)
  have hf : Function.Bijective f := by
    constructor
    · rintro (w|v) (w'|v') h <;> simp [f] at h ⊢
      · exact Subsingleton.elim _ _
      · exact h
    · rintro (_|p)
      · exact ⟨.infinite Rat.infinitePlace, rfl⟩
      · exact ⟨.finite (Rat.HeightOneSpectrum.primesEquiv.symm p), by simp [f]⟩
  have hh : ∀ v, (f v).hilbert a b = v.hilbert a b := by
    rintro (w|v)
    · have hw : w.IsReal := Subsingleton.elim Rat.infinitePlace w ▸ Rat.isReal_infinitePlace
      have := X (InfinitePlace.Completion.ringEquivRealOfIsReal hw) (algebraMap ℚ _ a) (algebraMap ℚ _ b)
      simp only [f, QuadFormsKB.RatPlace.hilbert, QuadFormsKB.NFPlace.hilbert, ← this]
      simp
    · have := X (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv (algebraMap ℚ _ a) (algebraMap ℚ _ b)
      simp only [f, QuadFormsKB.RatPlace.hilbert, QuadFormsKB.NFPlace.hilbert, ← this]
      simp
  have hS : {v : QuadFormsKB.RatPlace | v.hilbert a b = -1} = f '' {v : QuadFormsKB.NFPlace ℚ | v.hilbert a b = -1} := by
    ext r
    obtain ⟨v, rfl⟩ := hf.2 r
    simp [hf.1.eq_iff, hh]
  rw [hS]
  exact ⟨(Set.finite_image_iff hf.1.injOn).symm, (Set.ncard_image_of_injective _ hf.1).symm⟩

/-- **Hilbert reciprocity over $F = \mathbb{Q}$, number-field form:** the $F = \mathbb{Q}$ case of
`hilbert_reciprocity_nf`, from the proved `hilbert_product_formula` and the bridge. -/
@[kb "serre1973" "Ch. III §2.1, Thm. 3 [unverified]"]
theorem hilbert_reciprocity_nf_rat (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    {v : NFPlace ℚ | v.hilbert a b = -1}.Finite ∧
      Even {v : NFPlace ℚ | v.hilbert a b = -1}.ncard := by
  obtain ⟨hfin, hcard⟩ := hilbert_minus_one_rat_iff a b
  obtain ⟨f, e⟩ := hilbert_product_formula a b ha hb
  exact ⟨hfin.mpr f, hcard ▸ e⟩

/-- **Hasse–Minkowski over $F = \mathbb{Q}$, number-field form:** the $F = \mathbb{Q}$ case of
`hasseMinkowski_nf`, from `hasseMinkowski` and the bridge. -/
@[kb "serre1973" "Ch. IV §3.2, Thm. 8 [unverified]"]
theorem hasseMinkowski_nf_rat (Q : RatQF n) (hQ : Q.Nondegenerate) :
    Q.IsotropicIn ℚ ↔ NFPlace.Everywhere (F := ℚ) fun K _ _ => Q.IsotropicIn K := by
  rw [everywhere_isotropic_rat_iff]
  exact hasseMinkowski Q hQ

end QuadFormsKB
