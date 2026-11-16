import QuadFormsKB.Historical.Gauss.Genera
import QuadFormsKB.Literature.Cassels.Ch14.Thm51Groups530b

/-!
# Half of the assignable characters belong to genera (Disquisitiones Arithmeticae, Arts. 261-262)

(Art. 261: the number of genera of properly primitive forms of a nonsquare determinant
is at most half the number of assignable characters) and (Art. 262: if only two characters are
assignable, there is exactly one genus, the principal one, and the other character belongs to no form).

Gauss's properly primitive forms $(a, b, c)$ of determinant $D$ ($\gcd(a, 2b, c) = 1$, $b^2 - ac = D$) are exactly the
library's primitive forms of discriminant $4D$ (`Forms.lean`: `gaussForm`, `disc_gaussForm`); their proper classes are
`Composition.FormClass (4 * D)`.

Two formalizations of Gauss's "characters" are available in the library, and both are used:

* **Local form, every nonsquare determinant** (Cassels, Ch. 14, Thm. 5.1): a genus is a fibre of the homomorphism
  $\mathcal G \to \prod_{p \mid 2D} \mathcal G_p \times \mathcal G_\infty$ (`Composition.globalToLocal`) to the
  product of the groups of local classes; the image has index $2$ (`Composition.thm_5_1_nonsquare`). So exactly half
  of the a priori possible local data occur (`art261_half_local`), which is Art. 261 (at most half) together with
  Art. 287 III (at least half). Gauss counts positive forms only when $D < 0$; the local group at $\infty$ records the
  sign, so the statement counts positive and negative forms together, as Gauss does in Art. 264.
* **Characters, fundamental negative discriminants** (`Binary.formChar`): the product of the assigned characters is
  $1$ (`assigned_characters_product`), and the number of genera is $2^{t - 1}$ (`card_genera_eq`).

The identification of Gauss's characters with the local classes for an arbitrary determinant is not formalized
.
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary _root_.QuadFormsKB.Composition

/-- $4D$ is a nonzero discriminant when $D \ne 0$ (Gauss's determinant $D$, discriminant $4D$). -/
theorem nonzeroDisc_four_mul {D : ℤ} (hD : D ≠ 0) : NonzeroDisc (4 * D) :=
  ⟨mul_ne_zero four_ne_zero hD, Or.inl (Int.mul_emod_right 4 D)⟩

/-- $4D$ is a square only if $D$ is. -/
theorem not_isSquare_four_mul {D : ℤ} (hD : ¬ IsSquare D) : ¬ IsSquare (4 * D) := by
  rintro ⟨r, hr⟩
  have hev : Even (r * r) := ⟨2 * D, by rw [← hr]; ring⟩
  obtain ⟨s, rfl⟩ := Int.even_mul.mp hev |>.elim id id
  exact hD ⟨s, by linarith⟩

/-- **Gauss, *Disq. Arith.* Arts. 261 and 287 III, in local form (wrapper of
`Composition.thm_5_1_nonsquare`, Cassels Ch. 14, Thm. 5.1):** for a nonsquare determinant $D$, the genera of
properly primitive forms of determinant $D$ (the image of the classes in the product of the local class groups,
`Composition.globalToLocal`) are exactly half of all the a priori possible local data:
$$2 \cdot \#\{\text{genera}\} = \#\Bigl(\prod_{p \mid 2D} \mathcal G_p \times \mathcal G_\infty\Bigr).$$ -/
@[kb "gauss1801" "Arts. 261, 287 III"]
theorem art261_half_local {D : ℤ} [NonzeroDisc (4 * D)] (hD : ¬ IsSquare D) :
    Nat.card (MonoidHom.range (G := FormClass (4 * D)) (N := LocalProd (4 * D)) (globalToLocal (4 * D))) * 2 = Nat.card (LocalProd (4 * D)) := by
  rw [← thm_5_1_nonsquare (D := 4 * D) (not_isSquare_four_mul hD)]
  exact Subgroup.card_mul_index _

/-- **Gauss, *Disq. Arith.* Art. 261, at most half, in local form:** the number of genera
of properly primitive forms of a nonsquare determinant $D$ is at most half of the number of a priori possible local
data. -/
@[kb "gauss1801" "Art. 261"]
theorem art261_at_most_half_local {D : ℤ} [NonzeroDisc (4 * D)] (hD : ¬ IsSquare D) :
    2 * Nat.card (MonoidHom.range (G := FormClass (4 * D)) (N := LocalProd (4 * D)) (globalToLocal (4 * D))) ≤ Nat.card (LocalProd (4 * D)) := by
  rw [← art261_half_local hD, mul_comm]

/-- **Gauss, *Disq. Arith.* Art. 262, in local form:** if for the nonsquare determinant
$D$ only two local data are possible, all properly primitive forms of determinant $D$ lie in one genus. -/
@[kb "gauss1801" "Art. 262"]
theorem art262_one_genus_local {D : ℤ} [NonzeroDisc (4 * D)] (hD : ¬ IsSquare D)
    (h2 : Nat.card (LocalProd (4 * D)) = 2) (C₁ C₂ : FormClass (4 * D)) :
    globalToLocal (4 * D) C₁ = globalToLocal (4 * D) C₂ := by
  have h := art261_half_local hD
  rw [h2] at h
  have h1 : Nat.card (MonoidHom.range (G := FormClass (4 * D)) (N := LocalProd (4 * D)) (globalToLocal (4 * D))) = 1 := by omega
  have hsub := (Nat.card_eq_one_iff_unique.mp h1).1
  have := @Subsingleton.elim _ hsub ⟨_, MonoidHom.mem_range.mpr ⟨C₁, rfl⟩⟩
    ⟨_, MonoidHom.mem_range.mpr ⟨C₂, rfl⟩⟩
  exact congrArg Subtype.val this

/-- **Gauss, *Disq. Arith.* Art. 262, with characters, for a fundamental discriminant
$D < 0$ with one prime factor $p$ (e.g. Gauss's determinants $-1$ and $-2$, discriminants $-4$ and $-8$):** there is
exactly one genus of primitive positive definite forms, and the character $\chi_p = -1$ belongs to no form. -/
@[kb "gauss1801" "Art. 262"]
theorem art262_one_genus {D : ℤ} [IsQuadDisc D] (hD : D < 0) {p : ℕ} (hp : D.natAbs.primeFactors = {p}) :
    Nat.card (Genera D) = 1 ∧
      ∀ f : BinQF, Primitive f → f.disc = D → f.PosDef' → formChar f p = 1 := by
  refine ⟨by rw [card_genera_eq hD, hp, Finset.card_singleton]; rfl, fun f hf hfD hpos => ?_⟩
  have := assigned_characters_product hf hfD hpos
  rwa [hp, Finset.prod_singleton] at this

end QuadFormsKB.Historical.Gauss
