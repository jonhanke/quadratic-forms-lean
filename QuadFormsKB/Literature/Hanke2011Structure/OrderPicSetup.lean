/-
# The Picard group of an order: setup (Neukirch I (12.9)–(12.12))

**Setting.** $F$, $E$ number fields with $E/F$ (any degree), $\mathcal O = \mathcal O_E$, $R$ a subalgebra of $\mathcal O$ over
$\mathcal O_F$, $\mathfrak m \ne 0$ an ideal of $\mathcal O$ with $\mathfrak m \subseteq R$. Then $R$ has fraction field $E$
(`isFractionRing`), and $\mathcal O$ is integral over $R$.

**Defines**
* `restr`: an $\mathcal O$-fractional ideal of $E$, viewed as an $R$-fractional ideal (it is $R$-fractional because a nonzero
  $m\in\mathfrak m\subseteq R$ clears it into $\mathfrak m\subseteq R$);
* `extU`: $I\mapsto I\mathcal O$ on invertible fractional ideals (Mathlib's `FractionalIdeal.extendedHom`).

Source: Neukirch, *Algebraic Number Theory*, Ch. I, §12, (12.9)–(12.12), pp. 78–79.
-/
import QuadFormsKB.Literature.Hanke2011Structure.OrderClassNumber

open NumberField IsDedekindDomain FractionalIdeal
open scoped nonZeroDivisors

namespace QuadFormsKB.Hanke2011Structure.OrderCN

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]

/-- The fraction-field structure $R \to \mathcal O_E \to E$ of a subalgebra $R \subseteq \mathcal O_E$. -/
scoped instance algSubE (R : Subalgebra (𝓞 F) (𝓞 E)) : Algebra R E :=
  ((algebraMap (𝓞 E) E).comp (algebraMap R (𝓞 E))).toAlgebra

scoped instance (priority := high) towerRE (R : Subalgebra (𝓞 F) (𝓞 E)) : IsScalarTower R (𝓞 E) E :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The same tower with the scalar actions of the `Algebra` instances (Mathlib's lemmas on extended fractional
ideals elaborate them this way; `Subalgebra.instSMulSubtypeMem` is defeq but not reducibly). -/
scoped instance (priority := high) towerRE1 (R : Subalgebra (𝓞 F) (𝓞 E)) :
    @IsScalarTower R (𝓞 E) E (Subalgebra.toAlgebra R : Algebra R (𝓞 E)).toSMul
      (RingOfIntegers.instAlgebra_1 E).toSMul (algSubE R).toSMul := by
  letI := RingOfIntegers.instAlgebra_1 E
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl

scoped instance (priority := high) towerRE2 (R : Subalgebra (𝓞 F) (𝓞 E)) :
    @IsScalarTower R (𝓞 E) E (Subalgebra.toAlgebra R : Algebra R (𝓞 E)).toSMul
      (RingOfIntegers.instAlgebra (K := E) (L := E)).toSMul (algSubE R).toSMul := by
  letI := RingOfIntegers.instAlgebra (K := E) (L := E)
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl

variable (R : Subalgebra (𝓞 F) (𝓞 E))

theorem algebraMap_R_E (r : R) : algebraMap R E r = algebraMap (𝓞 E) E (r : 𝓞 E) := rfl

theorem algebraMap_R_E_injective : Function.Injective (algebraMap R E) := fun _ _ h =>
  Subtype.ext (IsFractionRing.injective (𝓞 E) E h)

instance : Algebra.IsIntegral R (𝓞 E) := Algebra.IsIntegral.tower_top (R := ℤ)

variable {R}

/-- **$E$ is the fraction field of $R$** when $R$ contains a nonzero ideal $\mathfrak m$ of $\mathcal O_E$. -/
theorem isFractionRing {𝔪 : Ideal (𝓞 E)} (h𝔪 : 𝔪 ≠ ⊥) (hR : ∀ x ∈ 𝔪, x ∈ R) : IsFractionRing R E := by
  obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔪
  refine ⟨fun s => ?_, fun z => ?_, fun {x y} h => ⟨1, by simpa using algebraMap_R_E_injective R h⟩⟩
  · refine IsUnit.mk0 _ ?_
    rw [algebraMap_R_E]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr
      (fun h => nonZeroDivisors.coe_ne_zero s (Subtype.ext h))
  · obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (𝓞 E)⁰ z
    have hb : (b : 𝓞 E) ≠ 0 := nonZeroDivisors.coe_ne_zero b
    refine ⟨⟨⟨a * m, hR _ (𝔪.mul_mem_left _ hm)⟩, ⟨⟨b * m, hR _ (𝔪.mul_mem_left _ hm)⟩,
      mem_nonZeroDivisors_of_ne_zero fun h => mul_ne_zero hb hm0 (congrArg Subtype.val h)⟩⟩, ?_⟩
    simp only [algebraMap_R_E, map_mul]
    rw [← mul_assoc, hab]

/-! ### Restricting $\mathcal O$-fractional ideals to $R$ -/

variable {𝔪 : Ideal (𝓞 E)}

theorem isFractional_restr [IsFractionRing R E] (h𝔪 : 𝔪 ≠ ⊥) (hR : ∀ x ∈ 𝔪, x ∈ R)
    (N : FractionalIdeal (𝓞 E)⁰ E) :
    IsFractional R⁰ ((N : Submodule (𝓞 E) E).restrictScalars R) := by
  obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔪
  obtain ⟨a, ha, hfr⟩ := N.isFractional
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  refine ⟨⟨m * a, hR _ (𝔪.mul_mem_right _ hm)⟩,
    mem_nonZeroDivisors_of_ne_zero fun h => mul_ne_zero hm0 ha0 (congrArg Subtype.val h), fun b hb => ?_⟩
  obtain ⟨o, ho⟩ := hfr b hb
  refine ⟨⟨m * o, hR _ (𝔪.mul_mem_right _ hm)⟩, ?_⟩
  rw [algebraMap_R_E, Algebra.smul_def, algebraMap_R_E]
  simp only [map_mul]
  rw [ho, Algebra.smul_def, mul_assoc]

/-- An $\mathcal O$-fractional ideal of $E$ as an $R$-fractional ideal. -/
def restr [IsFractionRing R E] (h𝔪 : 𝔪 ≠ ⊥) (hR : ∀ x ∈ 𝔪, x ∈ R) (N : FractionalIdeal (𝓞 E)⁰ E) :
    FractionalIdeal R⁰ E :=
  ⟨(N : Submodule (𝓞 E) E).restrictScalars R, isFractional_restr h𝔪 hR N⟩

theorem mem_restr [IsFractionRing R E] (h𝔪 : 𝔪 ≠ ⊥) (hR : ∀ x ∈ 𝔪, x ∈ R) (N : FractionalIdeal (𝓞 E)⁰ E)
    (x : E) : x ∈ restr h𝔪 hR N ↔ x ∈ N := Iff.rfl

/-! ### Extension of fractional ideals to $\mathcal O$ -/

variable (R) in
/-- **Extension** $I \mapsto I\mathcal O$ of invertible fractional ideals of $R$ to $\mathcal O_E$. -/
def extU [IsFractionRing R E] : (FractionalIdeal R⁰ E)ˣ →* (FractionalIdeal (𝓞 E)⁰ E)ˣ :=
  Units.map (FractionalIdeal.extendedHom (A := R) (K := E) E (𝓞 E)).toMonoidHom

theorem coe_extendedHom [IsFractionRing R E] (I : FractionalIdeal R⁰ E) :
    ((FractionalIdeal.extendedHom (A := R) (K := E) E (𝓞 E) I : FractionalIdeal (𝓞 E)⁰ E) :
      Submodule (𝓞 E) E) = Submodule.span (𝓞 E) (I : Set E) := by
  rw [coe_extendedHom_eq_span]
  congr 1
  ext x
  simp

end

end QuadFormsKB.Hanke2011Structure.OrderCN
