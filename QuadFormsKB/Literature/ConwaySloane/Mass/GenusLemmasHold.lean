/-
# Conway–Sloane 1988, §11: Lemmas 2–4 and their consequences, unconditional

J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices IV: the mass formula*, Proc. R. Soc. Lond. A **419** (1988),
259–286 (`conwaysloane1988`), §11 "Properties of the genus", pp. 280–281.

The four lemmas of §11 were first entered as named statements (`Lemma1Statement`, …, `Lemma4Statement`,
`GenusLemmas.lean`), and some consequences took them as hypotheses. All four are now theorems:
* Lemma 1: `lemma1Statement_proof` (`Section7HyperbolicMass.lean`);
* Lemma 2: `Gauss2.lemma2Statement_holds` (`GenusLemma2Local.lean`; the "only if" half `lemma2_only_if`, the "if" half
  at odd primes `lemma2_if_odd`, at $p = 2$ `Gauss2.lemma2IfDyadicRational` with the global step
  `qtwo_congrIn_of_discIso`);
* Lemma 3: `lemma3Statement_proof` (`GenusLemma3.lean`);
* Lemma 4: `Gauss2.lemma4Statement_holds` (from Lemmas 2 and 3).

This file states Lemmas 2 and 4 directly as equivalences with no hypotheses beyond the paper's (positive definite
integral lattices), and gives the unconditional versions of the consequences that took a lemma as a hypothesis.

**Conventions** (as in `GenusLemmas.lean`). A lattice is its integral Gram matrix `A : Matrix (Fin n) (Fin n) ℤ` with
`PosDefGram A`; $L \oplus I_1$ is `sumOne A`; the type $T$ is `gramType A` ($1$ odd, $2$ even); "an isomorphism
$L^*/L \cong M^*/M$ preserving norms mod $T$" is `DiscIso T A B`.

**Proves** (all unconditional)
* `lemma2` (§11, Lemma 2): same genus iff same type $T$ and an isomorphism of discriminant groups preserving norms
  mod $T$.
* `lemma3` (§11, Lemma 3), in the form of an implication.
* `lemma4` (§11, Lemma 4): same genus iff same type and an isomorphism preserving norms mod $1$.
* `sameGenus_of_discIso`: the "if" half of Lemma 2 (replaces `sameGenus_of_lemma4`, which assumed Lemma 4).
* `sameGenus_of_det_two'` (§11, remark 3): lattices of determinant $2$ and the same type are in the same genus
  (replaces `sameGenus_of_det_two`, which assumed Lemma 4); so there are at most two genera of determinant $2$ in each
  dimension.

Indices are 0-based.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.ConwaySloane.Mass.GenusLemma2Local

set_option linter.unusedSectionVars false

open Matrix QuadFormsKB QuadFormsKB.Siegel QuadFormsKB.LocalDensity QuadFormsKB.Tamagawa.Frames

namespace QuadFormsKB.ConwaySloane.Mass

variable {n : ℕ}

/-- **Conway–Sloane 1988, §11, Lemma 2** (unconditional): two positive definite integral lattices $L$, $M$ (Gram
matrices $A$, $B$ of the same dimension $n$) are in the same genus iff they have the same type $T$ and there is an
isomorphism $L^*/L \cong M^*/M$ preserving norms modulo $T$. -/
@[kb "conwaysloane1988" "§11, Lemma 2, p. 280 (proved)"]
theorem lemma2 {A B : Matrix (Fin n) (Fin n) ℤ} (hA : PosDefGram A) (hB : PosDefGram B) :
    SameGenus (ofMatrixZ A) (ofMatrixZ B) ↔ (gramType A = gramType B ∧ DiscIso (gramType A) A B) :=
  Gauss2.lemma2Statement_holds.iff n A B hA hB

/-- **Conway–Sloane 1988, §11, Lemma 3** (unconditional): if $L \oplus I_1$ and $M \oplus I_1$ are in the same genus
and $L$, $M$ have the same type, then $L$ and $M$ are in the same genus. -/
@[kb "conwaysloane1988" "§11, Lemma 3, p. 280 (proved)"]
theorem lemma3 {A B : Matrix (Fin n) (Fin n) ℤ} (hA : PosDefGram A) (hB : PosDefGram B)
    (h : SameGenus (ofMatrixZ (sumOne A)) (ofMatrixZ (sumOne B))) (ht : gramType A = gramType B) :
    SameGenus (ofMatrixZ A) (ofMatrixZ B) :=
  lemma3Statement_proof.imp n A B hA hB h ht

/-- **Conway–Sloane 1988, §11, Lemma 4** (unconditional): two positive definite integral lattices $L$, $M$ of the same
dimension are in the same genus iff they have the same type and there is an isomorphism $L^*/L \cong M^*/M$
preserving norms modulo $1$. -/
@[kb "conwaysloane1988" "§11, Lemma 4, p. 280 (proved)"]
theorem lemma4 {A B : Matrix (Fin n) (Fin n) ℤ} (hA : PosDefGram A) (hB : PosDefGram B) :
    SameGenus (ofMatrixZ A) (ofMatrixZ B) ↔ (gramType A = gramType B ∧ DiscIso 1 A B) :=
  Gauss2.lemma4Statement_holds.iff n A B hA hB

/-- **The "if" half of Lemma 2, unconditional**: same type $T$ and an isomorphism of the discriminant groups preserving
norms modulo $T$ give the same genus. (Unconditional version of `sameGenus_of_lemma4`.) -/
@[kb "conwaysloane1988" "§11, Lemma 2 (the \"if\" half), p. 280 (proved)"]
theorem sameGenus_of_discIso {A B : Matrix (Fin n) (Fin n) ℤ} (hA : PosDefGram A) (hB : PosDefGram B)
    (ht : gramType A = gramType B) (hi : DiscIso (gramType A) A B) :
    SameGenus (ofMatrixZ A) (ofMatrixZ B) :=
  sameGenus_of_lemma4 Gauss2.lemma4Statement_holds hA hB ht hi

/-- **§11, remark 3, unconditional** (p. 281): positive definite integral lattices of determinant $2$, the same
dimension and the same type are in the same genus; so in each dimension there are at most two genera of determinant
$2$, one for each type ($\mathrm I_n(2)$ and $\mathrm{II}_n(2)$ in the paper's notation). (Unconditional version of
`sameGenus_of_det_two`.) -/
@[kb "conwaysloane1988" "§11, remark 3, p. 281 (proved)"]
theorem sameGenus_of_det_two' {A B : Matrix (Fin n) (Fin n) ℤ} (hA : PosDefGram A) (hB : PosDefGram B)
    (dA : A.det = 2) (dB : B.det = 2) (ht : gramType A = gramType B) :
    SameGenus (ofMatrixZ A) (ofMatrixZ B) :=
  sameGenus_of_det_two Gauss2.lemma4Statement_holds hA hB dA dB ht

end QuadFormsKB.ConwaySloane.Mass
