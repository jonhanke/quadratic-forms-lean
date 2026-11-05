/-
# O'Meara §62: the squaring map of a finite field

**Setting.** $F$ is a finite field with $q$ elements (`[Fintype F]`, $q$ = `Fintype.card F`) of odd characteristic
(`hF : ringChar F ≠ 2`, O'Meara's standing assumption of Part Three). $\dot F = F^\times$ is the unit group `Fˣ`
and $\dot F^{2}$ is the range of the squaring homomorphism $\varphi : x \mapsto x^2$,
`(powMonoidHom 2 : Fˣ →* Fˣ)`.

**Proves** (O'Meara §62, p. 157, opening paragraph)
* `ker_sq_units`: the kernel of $\varphi$ is $\{1, -1\}$, and $1 \ne -1$;
* `card_sq_units`: $\dot F^{2}$ has $(q-1)/2$ elements (stated as $2\,\lvert\dot F^{2}\rvert = q - 1$);
* `index_sq_units`: $(\dot F : \dot F^{2}) = 2$.
-/
import Mathlib
import QuadFormsKB.Citation

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

variable {F : Type*} [Field F] [Fintype F]

/-- **The kernel of the squaring map** (O'Meara 1963, §62, p. 157): in a field $F$ of characteristic $\ne 2$ the
squaring homomorphism $\varphi : \dot F \to \dot F$, $x \mapsto x^2$, has kernel $\{\pm 1\}$, since $x^2 - 1 = 0$ has
exactly the roots $\pm 1$ and these are distinct. -/
@[kb "omeara1963" "§62, p. 157 (the squaring map of Ḟ has kernel {±1}, two distinct elements)"]
theorem ker_sq_units (hF : ringChar F ≠ 2) :
    ((powMonoidHom 2 : Fˣ →* Fˣ).ker : Set Fˣ) = {1, -1} ∧ (1 : Fˣ) ≠ -1 := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hne : (1 : Fˣ) ≠ -1 := by
    intro h
    have h' : ((1 : Fˣ) : F) = ((-1 : Fˣ) : F) := congrArg Units.val h
    simp only [Units.val_neg, Units.val_one] at h'
    exact h2 (by linear_combination h')
  refine ⟨?_, hne⟩
  ext x
  simp only [SetLike.mem_coe, MonoidHom.mem_ker, powMonoidHom_apply, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · intro h
    have h' : ((x : F) - 1) * ((x : F) + 1) = 0 := by
      have := congrArg Units.val h
      simp only [Units.val_pow_eq_pow_val, Units.val_one] at this
      linear_combination this
    rcases mul_eq_zero.1 h' with h1 | h1
    · left; ext; simpa [sub_eq_zero] using h1
    · right; ext; simp [eq_neg_of_add_eq_zero_left h1]
  · rintro (rfl | rfl) <;> simp

/-- **The number of squares** (O'Meara 1963, §62, p. 157): $\dot F^{2} = \varphi(\dot F)$ is a group of
$\tfrac12(q-1)$ elements, here $2\,\lvert\dot F^{2}\rvert = q - 1$, where $q$ is the number of elements of $F$. -/
@[kb "omeara1963" "§62, p. 157 (Ḟ² has (q − 1)/2 elements)"]
theorem card_sq_units (hF : ringChar F ≠ 2) :
    2 * Nat.card (powMonoidHom 2 : Fˣ →* Fˣ).range = Fintype.card F - 1 := by
  have hk := ker_sq_units (F := F) hF
  have hker : Nat.card (powMonoidHom 2 : Fˣ →* Fˣ).ker = 2 := by
    rw [show Nat.card (powMonoidHom 2 : Fˣ →* Fˣ).ker =
      Nat.card (((powMonoidHom 2 : Fˣ →* Fˣ).ker : Subgroup Fˣ) : Set Fˣ) from rfl,
      Nat.card_coe_set_eq, hk.1, Set.ncard_pair hk.2]
  have := Subgroup.card_ker_mul_card_range (powMonoidHom 2 : Fˣ →* Fˣ)
  rw [hker, Nat.card_units, Nat.card_eq_fintype_card (α := F)] at this
  omega

/-- **The index of the squares** (O'Meara 1963, §62, p. 157): $(\dot F : \dot F^{2}) = 2$; so every element of $F$ is
a square or a square times a fixed non-square. -/
@[kb "omeara1963" "§62, p. 157 ((Ḟ : Ḟ²) = 2)"]
theorem index_sq_units (hF : ringChar F ≠ 2) : (powMonoidHom 2 : Fˣ →* Fˣ).range.index = 2 := by
  have h1 := card_sq_units (F := F) hF
  have h2 := Subgroup.card_mul_index (powMonoidHom 2 : Fˣ →* Fˣ).range
  rw [Nat.card_units, Nat.card_eq_fintype_card (α := F)] at h2
  have hpos : 0 < Nat.card (powMonoidHom 2 : Fˣ →* Fˣ).range := Nat.card_pos
  have : Nat.card (powMonoidHom 2 : Fˣ →* Fˣ).range * (powMonoidHom 2 : Fˣ →* Fˣ).range.index =
      Nat.card (powMonoidHom 2 : Fˣ →* Fˣ).range * 2 := by rw [h2]; omega
  exact Nat.eq_of_mul_eq_mul_left hpos this

end QuadFormsKB.OMeara
