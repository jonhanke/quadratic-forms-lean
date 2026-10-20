/-
# The class group acting on left ideal classes

**Layer:** $F$ a number field (any class number), $D = (a,b)_F$, $\mathcal O$ an order of $D$; left ideals $J$ of $\mathcal O$ and their classes.

* **`scaleIdeal_cancel`**: $\mathfrak cJ = \mathfrak dJ \Rightarrow \mathfrak c = \mathfrak d$ ($\operatorname{nrd}J \ne 0$; apply $\operatorname{nrd}$, then $\mathfrak c^2 = \mathfrak d^2$ in
  the free monoid of ideals);
* `idealRel_scaleIdeal_of_mk0_eq`: $[\mathfrak a] = [\mathfrak a'] \in \mathrm{Cl}(F) \Rightarrow \mathfrak aJ \sim \mathfrak a'J$;
* **`clsAction`**: the action of $\mathrm{Cl}(F)$ on left ideal classes, $c\cdot[J] = [\mathfrak a_cJ]$ ($\mathfrak a_c$ = `clsIdeal c`), with
  `mk0_smul` ($[\mathfrak a]\cdot[J] = [\mathfrak aJ]$ for every nonzero $\mathfrak a$).

Source: Voight 2021, §§17.4, 26.5 (the class group acting on left classes; it is what makes $h_F$ appear in Eichler's mass formula)
[unverified locators].
-/
import QuadFormsKB.Tamagawa.EichlerMassNF

open NumberField IsDedekindDomain Quaternion
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat

attribute [-instance] NumberField.RingOfIntegers.instAlgebra

namespace Gen

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)}

/-! ### Cancellation -/

theorem cI_pow (v : HeightOneSpectrum (𝓞 F)) {𝔞 : Ideal (𝓞 F)} (h : 𝔞 ≠ ⊥) (k : ℕ) : cI v (𝔞 ^ k) = k * cI v 𝔞 := by
  unfold cI
  rw [Associates.mk_pow, Associates.count_pow (Associates.mk_ne_zero.2 h) v.associates_irreducible]

/-- **Squares of ideals are injective**: $\mathfrak c^2 = \mathfrak d^2 \Rightarrow \mathfrak c = \mathfrak d$ (Dedekind domain). -/
theorem eq_of_sq_eq {𝔠 𝔡 : Ideal (𝓞 F)} (h𝔠 : 𝔠 ≠ ⊥) (h𝔡 : 𝔡 ≠ ⊥) (h : 𝔠 ^ 2 = 𝔡 ^ 2) : 𝔠 = 𝔡 := by
  have hc : ∀ v : HeightOneSpectrum (𝓞 F), cI v 𝔠 = cI v 𝔡 := fun v => by
    have := congrArg (cI v) h
    rw [cI_pow v h𝔠, cI_pow v h𝔡] at this
    omega
  ext x
  rw [mem_iff_forall_cI h𝔠, mem_iff_forall_cI h𝔡]
  simp only [hc]

theorem scaleIdeal_eq_of_idealSet_eq {𝔠 𝔡 : Ideal (𝓞 F)} {J : Ideal O}
    (h : idealSet (scaleIdeal 𝔠 J) = idealSet (scaleIdeal 𝔡 J)) : scaleIdeal 𝔠 J = scaleIdeal 𝔡 J := by
  ext x
  rw [← coe_mem_idealSet, ← coe_mem_idealSet, h]

/-- **Cancellation:** $\mathfrak cJ = \mathfrak dJ$ (as sets) with $\operatorname{nrd}J \ne 0$ forces $\mathfrak c = \mathfrak d$. -/
theorem scaleIdeal_cancel (hO : IsOrder (𝓞 F) F O) {J : Ideal O} (hJ : leftNrdIdeal J ≠ ⊥) {𝔠 𝔡 : Ideal (𝓞 F)}
    (h𝔠 : 𝔠 ≠ ⊥) (h𝔡 : 𝔡 ≠ ⊥) (h : idealSet (scaleIdeal 𝔠 J) = idealSet (scaleIdeal 𝔡 J)) : 𝔠 = 𝔡 := by
  have h1 := congrArg leftNrdIdeal (scaleIdeal_eq_of_idealSet_eq h)
  rw [leftNrdIdeal_scaleIdeal hO, leftNrdIdeal_scaleIdeal hO] at h1
  exact eq_of_sq_eq h𝔠 h𝔡 (mul_right_cancel₀ hJ h1)

/-! ### Principal and equivalent scalings -/

theorem scaleSet_top (N : Submodule (𝓞 F) (QuatF F a b)) : scaleSet ⊤ (N : Set (QuatF F a b)) = N := by
  apply le_antisymm
  · rw [scaleSet, Submodule.span_le]
    rintro _ ⟨r, -, y, hy, rfl⟩
    exact N.smul_mem r hy
  · intro y hy
    have := smul_mem_scaleSet (𝔞 := ⊤) (S := (N : Set (QuatF F a b))) (Submodule.mem_top (x := (1 : 𝓞 F))) hy
    rwa [one_smul] at this

theorem idealSet_scaleIdeal_top (J : Ideal O) : idealSet (scaleIdeal ⊤ J) = idealSet J := by
  rw [idealSet_scaleIdeal, ← coe_idealSub, scaleSet_top]

theorem scaleIdeal_top (J : Ideal O) : scaleIdeal ⊤ J = J := by
  ext x
  rw [← coe_mem_idealSet, ← coe_mem_idealSet, idealSet_scaleIdeal_top]

/-- $(\mu)\mathfrak aJ = (\mathfrak aJ)\mu \sim \mathfrak aJ$. -/
theorem idealRel_scaleIdeal_span_mul {μ : 𝓞 F} (hμ : μ ≠ 0) (𝔞 : Ideal (𝓞 F)) (J : Ideal O) :
    IdealRel (scaleIdeal 𝔞 J) (scaleIdeal (Ideal.span {μ} * 𝔞) J) := by
  refine ⟨unitOf hμ, ?_⟩
  rw [idealSet_scaleIdeal, idealSet_scaleIdeal, ← scaleSet_scaleSet, scaleSet_span_singleton, unitOf_val]

theorem idealRel_trans {J₁ J₂ J₃ : Ideal O} (h₁ : IdealRel J₁ J₂) (h₂ : IdealRel J₂ J₃) : IdealRel J₁ J₃ :=
  (idealSetoid O).iseqv.trans h₁ h₂

theorem idealRel_symm {J₁ J₂ : Ideal O} (h : IdealRel J₁ J₂) : IdealRel J₂ J₁ := (idealSetoid O).iseqv.symm h

/-- **Equivalent ideals scale to equivalent left ideals:** $[\mathfrak a] = [\mathfrak a']$ in $\mathrm{Cl}(F)$ $\Rightarrow$
$\mathfrak aJ \sim \mathfrak a'J$. -/
theorem idealRel_scaleIdeal_of_mk0_eq {𝔞 𝔞' : (Ideal (𝓞 F))⁰} (h : ClassGroup.mk0 𝔞 = ClassGroup.mk0 𝔞') (J : Ideal O) :
    IdealRel (scaleIdeal (𝔞 : Ideal (𝓞 F)) J) (scaleIdeal (𝔞' : Ideal (𝓞 F)) J) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.1 h
  have h1 := idealRel_scaleIdeal_span_mul hx (𝔞 : Ideal (𝓞 F)) J
  have h2 := idealRel_scaleIdeal_span_mul hy (𝔞' : Ideal (𝓞 F)) J
  rw [hxy] at h1
  exact idealRel_trans h1 (idealRel_symm h2)

theorem classScale_eq_of_mk0_eq {𝔞 𝔞' : (Ideal (𝓞 F))⁰} (h : ClassGroup.mk0 𝔞 = ClassGroup.mk0 𝔞') :
    classScale (O := O) (𝔞 : Ideal (𝓞 F)) = classScale (𝔞' : Ideal (𝓞 F)) := by
  funext x
  induction x using Quotient.inductionOn with
  | h J => exact Quotient.sound (idealRel_scaleIdeal_of_mk0_eq h J)

theorem scaleIdeal_scaleIdeal (𝔞 𝔟 : Ideal (𝓞 F)) (J : Ideal O) :
    scaleIdeal 𝔞 (scaleIdeal 𝔟 J) = scaleIdeal (𝔞 * 𝔟) J := by
  ext x
  rw [← coe_mem_idealSet, ← coe_mem_idealSet, idealSet_scaleIdeal, idealSet_scaleIdeal, idealSet_scaleIdeal,
    scaleSet_scaleSet]

theorem classScale_mul (𝔞 𝔟 : Ideal (𝓞 F)) (x : Quotient (idealSetoid O)) :
    classScale (𝔞 * 𝔟) x = classScale 𝔞 (classScale 𝔟 x) := by
  induction x using Quotient.inductionOn with
  | h J => rw [classScale_mk, classScale_mk, classScale_mk, scaleIdeal_scaleIdeal]

theorem classScale_top (x : Quotient (idealSetoid O)) : classScale ⊤ x = x := by
  induction x using Quotient.inductionOn with
  | h J => rw [classScale_mk, scaleIdeal_top]

theorem clsIdeal_ne_bot' (c : ClassGroup (𝓞 F)) : ((clsIdeal c : (Ideal (𝓞 F))⁰) : Ideal (𝓞 F)) ≠ ⊥ :=
  mem_nonZeroDivisors_iff_ne_zero.1 (clsIdeal c).2

theorem mk0_clsIdeal (c : ClassGroup (𝓞 F)) : ClassGroup.mk0 (clsIdeal c) = c :=
  (ClassGroup.mk0_surjective c).choose_spec

/-! ### The action -/

/-- **The action of $\mathrm{Cl}(F)$ on left ideal classes**: $c\cdot[J] = [\mathfrak a_cJ]$. -/
instance clsAction : MulAction (ClassGroup (𝓞 F)) (Quotient (idealSetoid O)) where
  smul c x := classScale ((clsIdeal c : (Ideal (𝓞 F))⁰) : Ideal (𝓞 F)) x
  one_smul x := by
    change classScale _ x = x
    have h : ClassGroup.mk0 (clsIdeal (1 : ClassGroup (𝓞 F))) = ClassGroup.mk0 (1 : (Ideal (𝓞 F))⁰) := by
      rw [mk0_clsIdeal, map_one]
    rw [classScale_eq_of_mk0_eq h, Submonoid.coe_one, Ideal.one_eq_top]
    exact classScale_top x
  mul_smul c d x := by
    change classScale _ x = classScale _ (classScale _ x)
    have h : ClassGroup.mk0 (clsIdeal (c * d)) = ClassGroup.mk0 (clsIdeal c * clsIdeal d) := by
      rw [mk0_clsIdeal, map_mul, mk0_clsIdeal, mk0_clsIdeal]
    rw [classScale_eq_of_mk0_eq h, ← classScale_mul]
    rfl

theorem cls_smul_def (c : ClassGroup (𝓞 F)) (x : Quotient (idealSetoid O)) :
    c • x = classScale ((clsIdeal c : (Ideal (𝓞 F))⁰) : Ideal (𝓞 F)) x := rfl

/-- **$[\mathfrak a]\cdot[J] = [\mathfrak aJ]$** for every nonzero integral ideal $\mathfrak a$. -/
theorem mk0_smul (𝔞 : (Ideal (𝓞 F))⁰) (x : Quotient (idealSetoid O)) :
    ClassGroup.mk0 𝔞 • x = classScale (𝔞 : Ideal (𝓞 F)) x := by
  rw [cls_smul_def]
  exact congrFun (classScale_eq_of_mk0_eq (mk0_clsIdeal _)) x

theorem mk0_smul_mk (𝔞 : (Ideal (𝓞 F))⁰) (J : Ideal O) :
    ClassGroup.mk0 𝔞 • (Quotient.mk (idealSetoid O) J) = Quotient.mk (idealSetoid O) (scaleIdeal (𝔞 : Ideal (𝓞 F)) J) := by
  rw [mk0_smul, classScale_mk]

/-- The nonzero ideal $\mathfrak a$ as an element of $(\mathrm{Ideal}\ \mathcal O_F)^0$. -/
def nzIdeal {𝔞 : Ideal (𝓞 F)} (h : 𝔞 ≠ ⊥) : (Ideal (𝓞 F))⁰ := ⟨𝔞, mem_nonZeroDivisors_iff_ne_zero.2 h⟩

@[simp] theorem coe_nzIdeal {𝔞 : Ideal (𝓞 F)} (h : 𝔞 ≠ ⊥) : ((nzIdeal h : (Ideal (𝓞 F))⁰) : Ideal (𝓞 F)) = 𝔞 := rfl

/-- **The orbit relation of the class-group action:** $[J'] \in \mathrm{Cl}(F)\cdot[J]$ iff $\mathfrak aJ \sim \mathfrak bJ'$ for nonzero integral
$\mathfrak a, \mathfrak b$. -/
theorem exists_smul_eq_iff (J J' : Ideal O) :
    (∃ c : ClassGroup (𝓞 F), c • Quotient.mk (idealSetoid O) J = Quotient.mk (idealSetoid O) J') ↔
      ∃ 𝔞 𝔟 : Ideal (𝓞 F), 𝔞 ≠ ⊥ ∧ 𝔟 ≠ ⊥ ∧ IdealRel (scaleIdeal 𝔞 J) (scaleIdeal 𝔟 J') := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨clsIdeal c, ⊤, clsIdeal_ne_bot' c, top_ne_bot, ?_⟩
    rw [scaleIdeal_top]
    rw [cls_smul_def, classScale_mk] at hc
    exact Quotient.exact hc
  · rintro ⟨𝔞, 𝔟, h𝔞, h𝔟, hrel⟩
    refine ⟨ClassGroup.mk0 (nzIdeal h𝔞) * (ClassGroup.mk0 (nzIdeal h𝔟))⁻¹, ?_⟩
    apply classScale_injective (O := O) h𝔟
    have e : ∀ y : Quotient (idealSetoid O), classScale 𝔟 y = ClassGroup.mk0 (nzIdeal h𝔟) • y :=
      fun y => by rw [mk0_smul, coe_nzIdeal]
    have hc : ClassGroup.mk0 (nzIdeal h𝔟) * (ClassGroup.mk0 (nzIdeal h𝔞) * (ClassGroup.mk0 (nzIdeal h𝔟))⁻¹) =
        ClassGroup.mk0 (nzIdeal h𝔞) := by
      rw [mul_comm (ClassGroup.mk0 (nzIdeal h𝔟)), mul_assoc, inv_mul_cancel, mul_one]
    rw [e, e, smul_smul, hc, mk0_smul_mk, mk0_smul_mk]
    exact Quotient.sound hrel

end Gen

end QuadFormsKB.QuatOrder
