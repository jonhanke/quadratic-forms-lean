/-
# Cassels, Chapter 14: further citations and two small statements

Declarations that state items of Chapter 14 but carried no Chapter 14 tag yet.
The tags are added with `attribute [kb …]`; (1.7) and (5.5), which had no standalone statement in the
library, are stated and proved here.
-/
import QuadFormsKB.Equiv.Binary
import QuadFormsKB.Binary.GenusDuplication
import QuadFormsKB.Binary.FormsIdeals
import QuadFormsKB.Binary.ClassBijection
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowski
import QuadFormsKB.Siegel.ThetaCharacter

namespace QuadFormsKB

/-- **Cassels, Ch. 14, (1.7)** (p. 331): *the middle coefficient $b$ of an integral binary form $[a, b, c]$ has the
parity of its discriminant $D = b^2 - 4ac$.* -/
@[kb "cassels1978" "Ch. 14, §1, (1.7), p. 331 (b ≡ D mod 2)"]
theorem BinQF.disc_emod_two (f : BinQF) : f.disc % 2 = f.b % 2 := by
  simp only [BinQF.disc]
  rcases Int.even_or_odd f.b with ⟨k, hk⟩ | ⟨k, hk⟩ <;> rw [hk] <;> ring_nf <;> omega

/-- **Cassels, Ch. 14, (5.5)** (p. 344): *for an odd prime $p$, $(-1/p) = +1$ if $p \equiv 1 \pmod 4$ and $-1$ if
$p \equiv -1 \pmod 4$* ("taken as known"; Mathlib's `legendreSym.at_neg_one`). The display is lost in the
machine-read text and was read from the page image. -/
@[kb "cassels1978" "Ch. 14, §5, (5.5), p. 344 ((−1/p) = ±1 according as p ≡ ±1 mod 4)"]
theorem Composition.legendreSym_neg_one (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    legendreSym p (-1) = if p % 4 = 1 then 1 else -1 := by
  rw [legendreSym.at_neg_one hp, ZMod.χ₄_nat_eq_if_mod_four]
  have h2 : p % 2 = 1 := Nat.odd_iff.1 ((Fact.out : p.Prime).odd_of_ne_two hp)
  have : p % 4 = 1 ∨ p % 4 = 3 := by omega
  rcases this with h | h <;> simp [h, show p % 2 ≠ 0 by omega]

attribute [kb "cassels1978" "Ch. 14, §1, (1.5), p. 331 (D = −4d(f), d the determinant)"]
  BinQF.disc_eq_neg_det_hessian
attribute [kb "cassels1978" "Ch. 14, proof of Lemma 4.1, (4.2), p. 341 (an improper automorph has trace 0, so S² = I)"]
  Binary.improper_trace_zero
attribute [kb "cassels1978" "Ch. 14, proof of Lemma 4.1, p. 341 (an ambiguous class contains a form with a ∣ b; positive definite)"]
  Binary.exists_sLEquiv_a_dvd_b
attribute [kb "cassels1978" "Ch. 14, §7, p. 354 (the weak Hasse principle: everywhere locally trivial is trivial)"]
  isometric_iff_everywhere
attribute [kb "cassels1978" "Ch. 14, Notes, pp. 354–355 (the ring of integers 𝐙[ω] of 𝐐(√D); fundamental D)"]
  Binary.QOrder
attribute [kb "cassels1978" "Ch. 14, Notes, p. 355 (N(xα + yβ) = j f(x, y) for a basis α, β of an ideal)"]
  Binary.IsFormOf
attribute [kb "cassels1978" "Ch. 14, Notes, p. 355 (the ideal of a form)"] Binary.formIdeal
attribute [kb "cassels1978" "Ch. 14, Notes, p. 355 (the norm of the ideal of a form)"] Binary.absNorm_formIdeal
attribute [kb "cassels1978" "Ch. 14, Notes, p. 355 (a basis l, m + nω of an ideal)"]
  Binary.exists_eq_span_mul_formIdeal
attribute [kb "cassels1978" "Ch. 14, Notes, p. 355 (an ideal determines a form)"] Binary.exists_isFormOf
attribute [kb "cassels1978" "Ch. 14, Thm. 2.1, proof, p. 337 (finiteness: the number of proper classes; D < 0 fundamental)"]
  Binary.card_slClasses
attribute [kb "cassels1978" "Ch. 14, Ex. 2, p. 358 (the Kronecker symbol (D/b) for every discriminant D)"]
  Siegel.kroneckerSym

end QuadFormsKB
