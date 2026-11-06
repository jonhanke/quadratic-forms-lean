/-
# Conway–Sloane, Ch. 15, §9.7: when is there only one class in the genus?

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.7, pp. 393–396
(`conwaysloane1999`).

**Status.** Conway–Sloane prove Theorems 19–21 and Corollary 22 from Eichler's theorem (their Thm. 14, proved in the
library: `Lattices.eichler_spinorGenus_eq_class_uncond`) and from Watson's description of the spinor kernel and of the
$p$-adically automorphous numbers (their Thms. 15–18 and the algorithm of §9.5, quoted from Watson 1960, Thms. 70 and 81,
without proof). The spinor-operator formalism of §9.4 and the algorithm are not formalized here, so Theorem 21 and
Corollary 22 are **stated, not proved** (`Theorem21Statement`, `Corollary22Statement`). The weaker form that the book
says Theorem 21 strengthens (Watson 1960, Cor. 1 and 2 to Thm. 69; Cassels Ch. 11, Thms. 1.3 and 1.5) is proved in the
library and is tagged here (`Lattices.isProperIsometric_of_sameGenus_of_det`,
`Lattices.exists_dvd_det_of_one_lt_properSpinorGenusNumber`).

**Conventions.** A form is its symmetric integer Gram matrix $A$ ($f(x) = xAx^{\mathsf T}$, classically integral, as in
the book), with the library form `Cassels.Ch8Ex2.gramForm A`; the determinant is $d = \det A$; the genus is
`Siegel.SameGenus` (equivalence over $\mathbb R$ and every $\mathbb Z_p$) and the class is $\mathbb Z$-equivalence
(`Siegel.IntEquiv`). "Indefinite" is `Lattices.IsIndefinite` of the rational form.
-/
import QuadFormsKB.Literature.ConwaySloane.Theorem11
import QuadFormsKB.Literature.Cassels.Ch11Thm13
import QuadFormsKB.Lattices.SpinorLocal
import QuadFormsKB.Literature.Cassels.Ch11Sec3Local

namespace QuadFormsKB.ConwaySloane

open Siegel Lattices Matrix

/-- The genus of the classically integral form with Gram matrix $A$ contains more than one class: some form with a
symmetric integer Gram matrix in the same genus is not $\mathbb Z$-equivalent to it. -/
def MoreThanOneClass {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∃ B : Matrix (Fin n) (Fin n) ℤ, Bᵀ = B ∧ SameGenus (Cassels.Ch8Ex2.gramForm A) (Cassels.Ch8Ex2.gramForm B) ∧
    ¬ IntEquiv (Cassels.Ch8Ex2.gramForm A) (Cassels.Ch8Ex2.gramForm B)

/-- **Theorem 21** (Conway–Sloane, §9.7, p. 395), *stated*: if $f$ is an indefinite form of dimension $n$ and
determinant $d$ with more than one class in its genus, then $4^{[n/2]}d$ is divisible by $k^{\binom n2}$ for some
nonsquare natural number $k \equiv 0$ or $1 \pmod 4$ (43). Not proved here (see the file header). -/
@[kb "conwaysloane1999" "Ch. 15, §9.7, Thm. 21, (43), p. 395 (stated)"]
def Theorem21Statement : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ), Aᵀ = A → A.det ≠ 0 →
    IsIndefinite ((Cassels.Ch8Ex2.gramForm A).map (Int.castRingHom ℚ)) → MoreThanOneClass A →
    ∃ k : ℕ, ¬ IsSquare k ∧ (k % 4 = 0 ∨ k % 4 = 1) ∧ (k : ℤ) ^ (n.choose 2) ∣ 4 ^ (n / 2) * A.det

/-- The bound $d_0(n)$ of Corollary 22: $17$ ($n = 2$), $128$ ($n = 3$), $5^{\binom n2}$ ($n \ge 4$ even),
$2 \cdot 5^{\binom n2}$ ($n \ge 5$ odd). -/
def d0 (n : ℕ) : ℕ :=
  if n = 2 then 17 else if n = 3 then 128 else if n % 2 = 0 then 5 ^ (n.choose 2) else 2 * 5 ^ (n.choose 2)

/-- **Corollary 22** (Conway–Sloane, §9.7, p. 395), *stated*: an indefinite form of dimension $n \ge 2$ and determinant
$d$ with more than one class in its genus has $\lvert d\rvert \ge d_0(n)$. Not proved here. -/
@[kb "conwaysloane1999" "Ch. 15, §9.7, Cor. 22, p. 395 (stated)"]
def Corollary22Statement : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ), 2 ≤ n → Aᵀ = A → A.det ≠ 0 →
    IsIndefinite ((Cassels.Ch8Ex2.gramForm A).map (Int.castRingHom ℚ)) → MoreThanOneClass A →
    d0 n ≤ A.det.natAbs

attribute [kb "conwaysloane1999" "Ch. 15, §9.7, p. 395 (the weaker form [Wat3, Cor. 1, 2 to Thm. 69] that Thm. 21 strengthens; via Cassels Ch. 11, Thm. 1.5)"]
  Lattices.isProperIsometric_of_sameGenus_of_det

attribute [kb "conwaysloane1999" "Ch. 15, §9.7, p. 395 (the weaker form [Wat3, Cor. 1, 2 to Thm. 69] of Thm. 21, for spinor genera; via Cassels Ch. 11, Thm. 1.3)"]
  Lattices.exists_dvd_det_of_one_lt_properSpinorGenusNumber

attribute [kb "conwaysloane1999" "Ch. 15, §9.6, p. 392 (irrelevant primes: every unit is the spinor norm of an integral automorph; containment only, the equality is not formalized)"]
  Lattices.spinorNorm_stdStab_unit

attribute [kb "conwaysloane1999" "Ch. 15, §9.7, Thm. 20 (a), (40), p. 393 (generalization, lattice form: the hypothesis 'not every p-adic unit is p-adically automorphous' is implied by intractability)"]
  Lattices.valued_det_le_of_not_units_mem

/-- The values of $d_0$ in the table of Corollary 22 for $n = 2, \dots, 5$. -/
example : d0 2 = 17 ∧ d0 3 = 128 ∧ d0 4 = 5 ^ 6 ∧ d0 5 = 2 * 5 ^ 10 := by decide

end QuadFormsKB.ConwaySloane
