/-
# Cassels, Chapter 14: named statements (results stated, not proved here)

Cassels, *Rational Quadratic Forms* (1978), Ch. 14. The results below are stated faithfully as named statements
(`Prop` structures with a source tag; never axioms), because their proofs are not formalized here. Everything
in this file that follows from them is proved.

* §3, p. 339 (14.r22): the set $\mathcal G_p$ of $\mathbb Z_p$-classes is a group and $\mathcal G \to \mathcal G_p$ is
  a homomorphism. The substance is that the $\mathbb Z_p$-class of a composition depends only on the
  $\mathbb Z_p$-classes of the factors (`LocalCompositionWellDefined`); from it, the $\mathbb Z_p$-class of a square
  is the class of the principal form (`isometricGL_principal_of_sq`), i.e. the image of $\mathcal G$ in
  $\mathcal G_p$ has exponent $2$ (Cassels' "every element of $\mathcal G_p$ other than the identity has order $2$").
* §6, pp. 351–353 (14.r39, 14.r42), $D = 4rs$ with primes $r \equiv s \equiv 1 \pmod 4$: the existence of the
  representation (6.24) when $(r/s) = 1$ (`FourRSRepresentation`, with the consequence
  `exists_rep_legendreSym_eq_condBiquadSym`), the case (ii) insolubility of $x^2 - rsy^2 = -1$
  (`FourRSCaseTwoNegPell`, with the consequence `exists_rep_one_of_caseTwo`: $rx^2 - sy^2 = 1$ is soluble), and the
  structure of the $2$-component of the class group (`FourRSTwoComponent`).
* Examples 5, 6 and 7 (iii), pp. 359–361: `NagellOrderN`, `NagellOrderNFundamental` (with
  `NagellOrderNFundamental.toNagellOrderN`), `PrincipalGenusRepCriterion`, `Ex7ClassRelation`.
-/
import QuadFormsKB.Literature.Cassels.Ch14.GaussComposition
import QuadFormsKB.Literature.Cassels.Ch14.Genus
import QuadFormsKB.Literature.Cassels.Ch14.Ambiguous
import QuadFormsKB.Literature.Cassels.Ch14.Biquadratic

namespace QuadFormsKB.Composition

open BinQF Binary FormClass Siegel

/-! ### §3: the group $\mathcal G_p$ -/

/-- **Named statement: composition is well defined on $\mathbb Z_p$-classes** (Cassels, Ch. 14, §3, p. 339: "the set
$\mathcal G_p$ … is a natural abelian group … there are natural homomorphisms $\mathcal G \to \mathcal G_p$" (3.1),
"by mimicking the argument of Section 2"). For primitive forms of discriminant $D$: if $f_1 \sim g_1$ and
$f_2 \sim g_2$ over $\mathbb Z_p$, and $F, G$ represent the compositions of the classes of $f_1, f_2$ and of $g_1, g_2$,
then $F \sim G$ over $\mathbb Z_p$ ($\mathrm{GL}_2(\mathbb Z_p)$-equivalence, which for these forms is the same as
proper equivalence, `isometricGL_iff_proper`). Field: `compat`. -/
@[kb "cassels1978" "Ch. 14, §3, p. 339, (3.1) (𝒢_p is a group and 𝒢 → 𝒢_p a homomorphism)"]
structure LocalCompositionWellDefined (p : ℕ) [Fact p.Prime] (D : ℤ) [NonzeroDisc D] : Prop where
  /-- The $\mathbb Z_p$-class of a composition depends only on the $\mathbb Z_p$-classes of the factors. -/
  compat : ∀ f₁ f₂ g₁ g₂ F G : PrimForm D,
    IsometricGL (f₁.1.map (Int.castRingHom ℤ_[p])) (g₁.1.map (Int.castRingHom ℤ_[p])) →
    IsometricGL (f₂.1.map (Int.castRingHom ℤ_[p])) (g₂.1.map (Int.castRingHom ℤ_[p])) →
    mk F = mk f₁ * mk f₂ → mk G = mk g₁ * mk g₂ →
    IsometricGL (F.1.map (Int.castRingHom ℤ_[p])) (G.1.map (Int.castRingHom ℤ_[p]))

/-- **The $\mathbb Z_p$-class of a square is the principal class** (Cassels, Ch. 14, §3, p. 339: every element of
$\mathcal G_p$ has order at most $2$, here for the image of $\mathcal G$), *conditional on*
`LocalCompositionWellDefined`. Proof: $f^{-1} = [a, -b, c]$ is $\mathrm{GL}_2(\mathbb Z)$-equivalent to $f$, so
$\mathfrak C^2$ and $\mathfrak C\mathfrak C^{-1} = \mathfrak E$ have the same $\mathbb Z_p$-class. -/
@[kb "cassels1978" "Ch. 14, §3, p. 339 (elements of 𝒢_p have order ≤ 2)"]
theorem isometricGL_principal_of_sq {p : ℕ} [Fact p.Prime] {D : ℤ} [NonzeroDisc D]
    (hW : LocalCompositionWellDefined p D) (f F : PrimForm D) (hF : mk F = mk f ^ 2) :
    IsometricGL (F.1.map (Int.castRingHom ℤ_[p])) ((principal D).1.map (Int.castRingHom ℤ_[p])) := by
  let g : PrimForm D := ⟨conjForm f.1, isPrimitive_conjForm f.2.1, (disc_conjForm f.1).trans f.2.2⟩
  have hI : IntEquiv f.1 g.1 := (intEquiv_iff_sLEquiv_or f.1 g.1).2 (Or.inr (SLEquiv.refl _))
  refine hW.compat f f f g F (principal D) (IsometricGL.refl _) (hI.sameGenus.1 p) (by rw [hF, pow_two]) ?_
  rw [mk_principal, ← mk_inv f]
  exact (mul_inv_cancel _).symm

/-! ### §6: the example $D = 4rs$ -/

/-- **Named statement: the representation (6.24)** (Cassels, Ch. 14, §6, p. 351): *for distinct primes
$r \equiv s \equiv 1 \pmod 4$ with $(r/s) = 1$, all forms of $\mathcal B$ are in the principal genus; in particular
there are an integer $w$ prime to $2rs$ and coprime integers $x, y$ with $f(r)(x, y) = rx^2 - sy^2 = w^2$.*
(Cassels: $f(r) = [r, 0, -s]$ is in the principal genus, hence a square by Theorem 3.1, hence represents
primitively some $w^2$ with $w$ prime to $2D$ by Lemma 2.5.) Field: `rep`. -/
@[kb "cassels1978" "Ch. 14, §6, (6.24), p. 351"]
structure FourRSRepresentation : Prop where
  /-- The representation $rx^2 - sy^2 = w^2$ with $\gcd(x, y) = 1$ and $w$ prime to $2rs$. -/
  rep : ∀ (r s : ℕ) [Fact r.Prime] [Fact s.Prime], r % 4 = 1 → s % 4 = 1 → r ≠ s → legendreSym s r = 1 →
    ∃ x y w : ℤ, IsCoprime x y ∧ IsCoprime w (2 * r * s) ∧ (r : ℤ) * x ^ 2 - s * y ^ 2 = w ^ 2

/-- **The genus character of $\mathfrak C_r$ is $[s/r]_4$** (Cassels, Ch. 14, §6, pp. 351–352: "$f(r)$ is in a class
$\mathfrak C_r^2$ … with character $\varepsilon_r = [s/r]_4$"), in the form: *there is $w$ prime to $2rs$ with
$rx^2 - sy^2 = w^2$ primitively and $(w/r) = [s/r]_4$*, conditional on `FourRSRepresentation`, by (6.25)
(`legendreSym_eq_condBiquadSym`). -/
@[kb "cassels1978" "Ch. 14, §6, p. 352 (ε_r = [s/r]₄)"]
theorem exists_rep_legendreSym_eq_condBiquadSym (hR : FourRSRepresentation) {r s : ℕ} [Fact r.Prime]
    [Fact s.Prime] (hr : r % 4 = 1) (hs : s % 4 = 1) (hrs : r ≠ s) (hη : legendreSym s r = 1) :
    ∃ x y w : ℤ, IsCoprime x y ∧ IsCoprime w (2 * r * s) ∧ (r : ℤ) * x ^ 2 - s * y ^ 2 = w ^ 2 ∧
      legendreSym r w = condBiquadSym r s := by
  obtain ⟨x, y, w, hxy, hw, h⟩ := hR.rep r s hr hs hrs hη
  exact ⟨x, y, w, hxy, hw, h, legendreSym_eq_condBiquadSym hr hs hrs hη hxy h hw⟩

/-- **Named statement: case (ii), the negative Pell equation is insoluble** (Cassels, Ch. 14, §6, pp. 352–353, case
(ii)): *for distinct primes $r \equiv s \equiv 1 \pmod 4$ with $(r/s) = 1$, $[s/r]_4 = +1$ and $[r/s]_4 = -1$, the
equation $x^2 - rsy^2 = -1$ is not soluble* (a case of Scholz's reciprocity law). Field: `not_negPell`. -/
@[kb "cassels1978" "Ch. 14, §6, pp. 352–353, case (ii) (x² − rsy² = −1 is not soluble)"]
structure FourRSCaseTwoNegPell : Prop where
  /-- $x^2 - rsy^2 = -1$ has no integral solution in case (ii). -/
  not_negPell : ∀ (r s : ℕ) [Fact r.Prime] [Fact s.Prime], r % 4 = 1 → s % 4 = 1 → r ≠ s →
    legendreSym s r = 1 → condBiquadSym r s = 1 → condBiquadSym s r = -1 →
    ¬ ∃ x y : ℤ, x ^ 2 - (r * s : ℤ) * y ^ 2 = -1

/-- **Case (ii): $rx^2 - sy^2 = 1$ is soluble** (Cassels, Ch. 14, §6, pp. 352–353, case (ii)), conditional on
`FourRSCaseTwoNegPell`. Proof: of the three possibilities of the descent (`negPell_trichotomy`), the negative
equation is excluded by the named statement and $su^2 - rv^2 = 1$ would make $r$ a fourth power modulo $s$. -/
@[kb "cassels1978" "Ch. 14, §6, pp. 352–353, case (ii) (rx² − sy² = 1 is soluble)"]
theorem exists_rep_one_of_caseTwo (hII : FourRSCaseTwoNegPell) {r s : ℕ} [Fact r.Prime] [Fact s.Prime]
    (hr : r % 4 = 1) (hs : s % 4 = 1) (hrs : r ≠ s) (hη : legendreSym s r = 1)
    (hεr : condBiquadSym r s = 1) (hεs : condBiquadSym s r = -1) :
    ∃ x y : ℤ, (r : ℤ) * x ^ 2 - s * y ^ 2 = 1 := by
  rcases negPell_trichotomy (Fact.out : r.Prime) (Fact.out : s.Prime) hr hs hrs with h1 | h1 | ⟨u, v, h1⟩
  · exact absurd h1 (hII.not_negPell r s hr hs hrs hη hεr hεs)
  · exact h1
  · have h4 := fourth_power hs hr u v h1
    have : condBiquadSym s r = 1 := by simp [condBiquadSym, h4]
    rw [this] at hεs
    norm_num at hεs

/-- **Named statement: the $2$-component of the class group for $D = 4rs$** (Cassels, Ch. 14, §6, pp. 351–353), for
distinct primes $r \equiv s \equiv 1 \pmod 4$, $\eta = (r/s)$, $\varepsilon_r = [s/r]_4$, $\varepsilon_s = [r/s]_4$:
the $2$-component of $\mathcal G$ is cyclic (`cyclic`); it has order exactly $2$ if $\eta = -1$ (`order_two`); it is
cyclic of order $4$ in cases (i) $\varepsilon_r = \varepsilon_s = -1$ and (ii) $\varepsilon_r\varepsilon_s = -1$
(`order_four`); it has order at least $8$ in case (iii) $\varepsilon_r = \varepsilon_s = +1$ (`order_ge_eight`).
The $2$-component is Mathlib's `CommGroup.primaryComponent`. -/
@[kb "cassels1978" "Ch. 14, §6, pp. 351–353 (the 2-component of the class group for D = 4rs)"]
structure FourRSTwoComponent : Prop where
  /-- The $2$-component is cyclic. -/
  cyclic : ∀ (r s : ℕ) [Fact r.Prime] [Fact s.Prime] [NonzeroDisc (4 * r * s)], r % 4 = 1 → s % 4 = 1 → r ≠ s →
    IsCyclic (CommGroup.primaryComponent (FormClass (4 * r * s)) 2)
  /-- $\eta = -1$: order $2$. -/
  order_two : ∀ (r s : ℕ) [Fact r.Prime] [Fact s.Prime] [NonzeroDisc (4 * r * s)], r % 4 = 1 → s % 4 = 1 →
    r ≠ s → legendreSym s r = -1 → Nat.card (CommGroup.primaryComponent (FormClass (4 * r * s)) 2) = 2
  /-- Cases (i) and (ii): order $4$. -/
  order_four : ∀ (r s : ℕ) [Fact r.Prime] [Fact s.Prime] [NonzeroDisc (4 * r * s)], r % 4 = 1 → s % 4 = 1 →
    r ≠ s → legendreSym s r = 1 → (condBiquadSym r s = -1 ∨ condBiquadSym s r = -1) →
    Nat.card (CommGroup.primaryComponent (FormClass (4 * r * s)) 2) = 4
  /-- Case (iii): order at least $8$. -/
  order_ge_eight : ∀ (r s : ℕ) [Fact r.Prime] [Fact s.Prime] [NonzeroDisc (4 * r * s)], r % 4 = 1 →
    s % 4 = 1 → r ≠ s → legendreSym s r = 1 → condBiquadSym r s = 1 → condBiquadSym s r = 1 →
    8 ≤ Nat.card (CommGroup.primaryComponent (FormClass (4 * r * s)) 2)

/-! ### Examples 5, 6, 7 (iii) -/

/-- **Named statement: Cassels, Ch. 14, Ex. 5 (i)** (p. 359, Nagell 1922): *for every $N > 1$ there is a
discriminant $D < 0$ whose class group $\mathcal G$ contains an element of order $N$.* Field: `exists_disc`. -/
@[kb "cassels1978" "Ch. 14, Ex. 5 (i), p. 359"]
structure NagellOrderN : Prop where
  /-- A discriminant $D < 0$ with an element of order $N$. -/
  exists_disc : ∀ N : ℕ, 1 < N → ∃ (D : ℤ) (_ : NonzeroDisc D), D < 0 ∧ ∃ C : FormClass D, orderOf C = N

/-- **Named statement: Cassels, Ch. 14, Ex. 5 (ii)** (p. 359): *the discriminant in Ex. 5 (i) can be taken
fundamental.* Field: `exists_disc`. -/
@[kb "cassels1978" "Ch. 14, Ex. 5 (ii), p. 359"]
structure NagellOrderNFundamental : Prop where
  /-- A fundamental discriminant $D < 0$ with an element of order $N$. -/
  exists_disc : ∀ N : ℕ, 1 < N → ∃ (D : ℤ) (_ : NonzeroDisc D), D < 0 ∧ Int.IsFundamentalDiscr D ∧
    ∃ C : FormClass D, orderOf C = N

/-- **Ex. 5 (ii) implies Ex. 5 (i).** -/
theorem NagellOrderNFundamental.toNagellOrderN (h : NagellOrderNFundamental) : NagellOrderN :=
  ⟨fun N hN => by
    obtain ⟨D, hD, hneg, -, C, hC⟩ := h.exists_disc N hN
    exact ⟨D, hD, hneg, C, hC⟩⟩

/-- **$f$ is primitively represented by $g = y^2 - xz$** (Cassels, Ch. 14, Ex. 6, p. 360, (£)): there is a basis
$\mathbf r, \mathbf s, \mathbf t$ of $\mathbb Z^3$ with $g(x\mathbf r + y\mathbf s) = f(x, y)$. -/
def PrimRepByY2XZ (f : BinQF) : Prop :=
  ∃ r s t : Fin 3 → ℤ, IsUnit (Matrix.of ![r, s, t]).det ∧ fOfRS r s = f

/-- **Named statement: Cassels, Ch. 14, Ex. 6** (p. 360): *a primitive integral form $f$ of discriminant $D \ne 0$
is in the principal genus if and only if it is primitively represented by $g(x, y, z) = y^2 - xz$.* *Erratum:*
Cassels writes "determinant $D = b^2 - 4ac$"; it is the discriminant. Field: `iff`. -/
@[kb "cassels1978" "Ch. 14, Ex. 6, p. 360"]
structure PrincipalGenusRepCriterion : Prop where
  /-- Principal genus iff primitively represented by $y^2 - xz$. -/
  iff : ∀ f : BinQF, f.IsPrimitive → f.disc ≠ 0 → (InPrincipalGenus f ↔ PrimRepByY2XZ f)

/-- **Named statement: Cassels, Ch. 14, Ex. 7 (iii)** (p. 361): *with $f = g(x\mathbf r + y\mathbf s)$ primitive
($\mathbf r, \mathbf s, \mathbf t$ a basis of $\mathbb Z^3$) and $h$ the form of Ex. 7, the classes satisfy
$\mathfrak C = \mathfrak D^{-2}$.* Field: `rel`. -/
@[kb "cassels1978" "Ch. 14, Ex. 7 (iii), p. 361"]
structure Ex7ClassRelation : Prop where
  /-- $\mathfrak C = \mathfrak D^{-2}$. -/
  rel : ∀ (r s t : Fin 3 → ℤ) (hb : IsUnit (Matrix.of ![r, s, t]).det) [NonzeroDisc (fOfRS r s).disc]
    (hf : (fOfRS r s).IsPrimitive),
    mk (⟨fOfRS r s, hf, rfl⟩ : PrimForm (fOfRS r s).disc) =
      (mk (⟨hOfRS r s, ex7_h_isPrimitive r s t hb, ex7_disc_h r s⟩ : PrimForm (fOfRS r s).disc))⁻¹ ^ 2

end QuadFormsKB.Composition
