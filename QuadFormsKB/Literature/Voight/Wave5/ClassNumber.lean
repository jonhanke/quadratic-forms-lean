/-
# Class numbers, type numbers and embedding numbers: statements (Voight, Chapters 25 and 30)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021 (key `voight2021`): Theorem 25.4.1 (p. 423),
Lemma 30.3.14 (p. 547), Corollary 30.4.18 (p. 550), Corollary 30.5.5 (p. 553), Lemma 30.6.17 (p. 557),
Proposition 30.8.5 and Main Theorem 30.8.6 (pp. 561-562), Proposition 30.9.2 (p. 563).

**Setting.** $F$ is a number field with ring of integers $R = \mathbb Z_F$, $B = (a, b)_F$ = `QuatF F a b`
($a, b \in \mathbb Z_F$ nonzero), $\mathcal O \subseteq B$ an order, $\operatorname{Cls}\mathcal O$ = `ClsO O`,
$\#\operatorname{Cls}\mathcal O$ = `clsNum O`, $\operatorname{mass}(\operatorname{Cls}\mathcal O)$ = `clsMass O`, and
$m(S, \mathcal O; \Gamma)$ = `embNum F S O Γ`. As in the earlier waves, classes are classes of left ideals and
$\mathcal O_R(J)$ (`rightOrder`) plays the role of the book's $\mathcal O_L(I)$.

**Quadratic orders.** The book's sums in 30.8 run over the quadratic $R$-orders $S$ (up to isomorphism). A quadratic order
that embeds in a division algebra is a domain, and its fraction field $K$ is a quadratic extension of $F$, hence embeds in
an algebraic closure $\overline F$. So the isomorphism classes that matter are those of the $R$-subalgebras
$S \subseteq \overline F$ that are finitely generated of rank $2$ (`QuadOrd F`), up to $R$-algebra isomorphism
(`QuadOrdCls F`); the quadratic algebras that are not domains ($K \cong F \times F$) do not embed in a totally definite
algebra and contribute $0$. Sums over `QuadOrdCls F` are `finsum`s: only finitely many terms are nonzero.

**Contents** (named propositions, not proved here unless said otherwise).
* `ClassNumberOneRat` (**Theorem 25.4.1**): a maximal order of a definite algebra over $\mathbb Q$ of discriminant $D$ has
  class number $1$ iff $D \in \{2, 3, 5, 7, 13\}$.
* `EmbNumIndexFormula F` (**Lemma 30.3.14**): $m(S, \mathcal O; \Gamma) = m(S, \mathcal O; \mathcal O^\times)\,
  [\operatorname{nrd}(\mathcal O^\times) : \operatorname{nrd}(\Gamma)\operatorname{nrd}(S^\times)]$ for $\mathcal O^1 \le \Gamma \le \mathcal O^\times$.
* `exists_embNum_ne_zero` (**Corollary 30.4.18**, **proved conditional on** `TraceFormulaEmb F`): if $S$ embeds optimally
  in every completion $\mathcal O_{\mathfrak p}$, some $\mathcal O_R(J)$, $[J] \in \operatorname{Cls}\mathcal O$, admits an optimal
  embedding of $S$.
* `LocalEmbNumFinite F` (**Corollary 30.5.5**): the local embedding numbers are finite.
* `LocalEmbNumEichlerOdd R F π` (**Lemma 30.6.17 (a), (b)**): explicit local embedding numbers of $\mathcal O_0(\pi^e)$.
* `UnitCountEmb F` (**Proposition 30.8.5**): $1 - \frac1{w_{\mathcal O}} = \frac12\sum_{q \ge 2}\left(1 - \frac1q\right)
  \sum_{[S^\times : R^\times] = q} m(S, \mathcal O; \mathcal O^\times)$.
* `EichlerClassNumberFormula F` (**Main Theorem 30.8.6**): $\#\operatorname{Cls}\mathcal O = \operatorname{mass}(\operatorname{Cls}\mathcal O)
  + \frac12\sum_{q \ge 2}\left(1 - \frac1q\right)\sum_{[S^\times:R^\times] = q} h(S)\, m(\widehat S, \widehat{\mathcal O};
  \widehat{\mathcal O}^\times)$.
* `DeuringTypeNumber` (**Proposition 30.9.2**): the type number of a maximal order in the definite algebra over $\mathbb Q$
  of prime discriminant $p$.

*Reading note (Main Theorem 30.8.6).* In the printed formula of Main Theorem 30.8.6 the
embedding number on the right is the adelic one $m(\widehat S, \widehat{\mathcal O}; \widehat{\mathcal O}^\times) =
\prod_{\mathfrak p} m(S_{\mathfrak p}, \mathcal O_{\mathfrak p}; \mathcal O_{\mathfrak p}^\times)$ of Theorem 30.4.7 (the proof ends "by
Theorem 30.4.7"); the hats mark the adelic number, and the statement here uses that product of local numbers.
-/
import QuadFormsKB.Literature.Voight.Wave4.OptimalEmbeddings
import QuadFormsKB.Literature.Voight.ClassNumberTrace

open NumberField IsDedekindDomain Quaternion

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Voight.Wave5

open QuadFormsKB.Quat QuadFormsKB.QuatOrder QuadFormsKB.Voight QuadFormsKB.Voight.Wave3 QuadFormsKB.Voight.Wave4

/-! ### Quadratic orders, unit indices, adelic embedding numbers -/

section Defs

variable (F : Type) [Field F] [NumberField F]

/-- **Quadratic orders that are domains**, as $\mathbb Z_F$-subalgebras $S \subseteq \overline F$ of an algebraic closure that
are finitely generated $\mathbb Z_F$-modules of rank $2$ (Voight 2021, 30.2-30.3: a quadratic $R$-order $S$ in a quadratic
field extension $K \supseteq F$). -/
@[kb "voight2021" "30.3.1, p. 545"]
def QuadOrd : Type :=
  {S : Subalgebra (𝓞 F) (AlgebraicClosure F) // Module.Finite (𝓞 F) S ∧ Module.finrank (𝓞 F) S = 2}

/-- Isomorphism of quadratic orders as $\mathbb Z_F$-algebras. -/
def quadOrdSetoid : Setoid (QuadOrd F) where
  r S T := Nonempty (S.1 ≃ₐ[𝓞 F] T.1)
  iseqv := ⟨fun S => ⟨AlgEquiv.refl⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

/-- **Isomorphism classes of quadratic orders** (domains) over $\mathbb Z_F$. -/
@[kb "voight2021" "30.8.1, p. 560"]
def QuadOrdCls : Type := Quotient (quadOrdSetoid F)

variable {F}

/-- **The unit index** $[S^\times : R^\times]$ of a quadratic order ($0$ if infinite, e.g. for real quadratic orders over
$\mathbb Q$). -/
@[kb "voight2021" "Proposition 30.8.5, p. 561"]
def unitIdx (S : QuadOrd F) : ℕ :=
  (Units.map (algebraMap (𝓞 F) S.1 : 𝓞 F →* S.1)).range.index

/-- **The class number** $h(S) = \#\operatorname{Pic}S$ of a quadratic order (Mathlib's `ClassGroup`). -/
@[kb "voight2021" "Theorem 30.4.7, p. 548"]
def quadClassNum (S : QuadOrd F) : ℕ := Nat.card (ClassGroup S.1)

/-- **The unit index of an order** $w_{\mathcal O} = [\mathcal O^\times : R^\times]$ (Voight 2021, 30.8): the index of
$R^\times$ in the unit group $\mathcal O^\times$, the stabilizer of the unit ideal $\mathcal O$ (`QuatOrder.rStab ⊤`). -/
@[kb "voight2021" "30.8, p. 560"]
def ordUnitIdx {a b : 𝓞 F} (O : Subalgebra (𝓞 F) (QuatF F a b)) : ℕ :=
  (centralUnitsIn (R := 𝓞 F) (⊤ : Ideal O)).index

/-- **The adelic embedding number** $m(\widehat S, \widehat{\mathcal O}; \widehat{\mathcal O}^\times) = \prod_{\mathfrak p}
m(S_{\mathfrak p}, \mathcal O_{\mathfrak p}; \mathcal O_{\mathfrak p}^\times)$ (Voight 2021, 30.4.5 and (30.7.2)), with completions
$S_{\mathfrak p} = \mathfrak o_{\mathfrak p} \otimes S$ and $\mathcal O_{\mathfrak p}$ = `localOrder`, as in `TraceFormulaEmb`. -/
@[kb "voight2021" "(30.7.2), p. 559"]
def adelicEmbNum {a b : 𝓞 F} (O : Subalgebra (𝓞 F) (QuatF F a b)) (S : Type) [CommRing S] [Algebra (𝓞 F) S] : ℕ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 F),
    embNum (v.adicCompletion F) (TensorProduct (𝓞 F) (v.adicCompletionIntegers F) S) (localOrder (v := v) a b O) ⊤

/-- The reduced norm $\operatorname{nrd} : B \to F$ as a monoid homomorphism (`Quat.nrd`). -/
def nrdHom (a b : 𝓞 F) : QuatF F a b →* F where
  toFun := nrd
  map_one' := nrd_one
  map_mul' := nrd_mul

/-- The reduced norm on the unit group of an order, $\mathcal O^\times \to F^\times$. -/
def nrdUnits {a b : 𝓞 F} (O : Subalgebra (𝓞 F) (QuatF F a b)) : Oˣ →* Fˣ :=
  Units.map ((nrdHom a b).comp O.val.toMonoidHom)

end Defs

/-! ### Theorem 25.4.1 -/

/-- **Maximal orders of class number one over $\mathbb Q$** (Voight 2021, Theorem 25.4.1), as a named proposition: let
$B = (a, b \mid \mathbb Q)$ be definite with discriminant $D = \prod_{p \in \operatorname{Ram}_f B} p$ and $\mathcal O \subset B$ a maximal
order. Then $\#\operatorname{Cls}\mathcal O = 1$ iff $D \in \{2, 3, 5, 7, 13\}$. Proved conditional on the Eichler
class number formula over $\mathbb Q$: `classNumberOneRat_of_eichlerClassNumberFormulaRat` (`Wave5/ClassNumberOne.lean`). -/
@[kb "voight2021" "Theorem 25.4.1, p. 423"]
def ClassNumberOneRat : Prop :=
  ∀ (a b : 𝓞 ℚ) (ha : a ≠ 0) (hb : b ≠ 0), IsTotDefinite a b →
    ∀ O : Subalgebra (𝓞 ℚ) (QuatF ℚ a b), IsMaximalOrder (𝓞 ℚ) ℚ O →
      (clsNum O = 1 ↔ ∏ v ∈ ramFin ha hb, Ideal.absNorm v.asIdeal ∈ ({2, 3, 5, 7, 13} : Finset ℕ))

/-! ### Lemma 30.3.14 and Corollary 30.5.5 -/

/-- **Comparison of embedding numbers** (Voight 2021, Lemma 30.3.14), as a named proposition about the number field $F$:
for an order $\mathcal O \subseteq B = (a, b)_F$, a quadratic $\mathbb Z_F$-order $S$ (free of rank $2$) and a subgroup
$\mathcal O^1 \le \Gamma \le \mathcal O^\times$ ($\mathcal O^1$ the units of reduced norm $1$),
$$m(S, \mathcal O; \Gamma) = m(S, \mathcal O; \mathcal O^\times)\,[\operatorname{nrd}(\mathcal O^\times) : \operatorname{nrd}(\Gamma)\operatorname{nrd}(S^\times)],$$
with $\operatorname{nrd}(S^\times) = \operatorname{N}_{K/F}(S^\times)$ (the reduced norm of $\varphi(s)$ is the norm of $s$ for every embedding
$\varphi$) and the index that of the subgroup generated by $\operatorname{nrd}(\Gamma)$ and $\operatorname{nrd}(S^\times)$ in
$\operatorname{nrd}(\mathcal O^\times) \le F^\times$ (`Subgroup.relIndex`). -/
@[kb "voight2021" "Lemma 30.3.14, p. 547"]
def EmbNumIndexFormula (F : Type) [Field F] [NumberField F] : Prop :=
  ∀ (a b : 𝓞 F), a ≠ 0 → b ≠ 0 → ∀ O : Subalgebra (𝓞 F) (QuatF F a b), IsOrder (𝓞 F) F O →
  ∀ (S : Type) [CommRing S] [IsDomain S] [Algebra (𝓞 F) S] [Module.Free (𝓞 F) S] [Module.Finite (𝓞 F) S],
    Module.finrank (𝓞 F) S = 2 → ∀ Γ : Subgroup Oˣ, (∀ u : Oˣ, nrdUnits O u = 1 → u ∈ Γ) →
      embNum F S O Γ = embNum F S O ⊤ *
        ((Γ.map (nrdUnits O)) ⊔ (Units.map ((algebraMap (𝓞 F) F : 𝓞 F →* F).comp
          (Algebra.norm (𝓞 F) (S := S)))).range).relIndex (nrdUnits O).range

/-- **Local embedding numbers are finite** (Voight 2021, Corollary 30.5.5), as a named proposition about the number field
$F$: for an order $\mathcal O \subseteq (a, b)_F$, a finite place $v$, a quadratic order $S$ and a subgroup $\Gamma$ with
$\mathcal O_v^1 \le \Gamma \le \mathcal O_v^\times$, the number $m(S_v, \mathcal O_v; \Gamma)$ of $\Gamma$-conjugacy classes of optimal
embeddings $S_v = \mathfrak o_v \otimes S \to \mathcal O_v$ is finite. (The book also allows $\Gamma \le N(\mathcal O_v)$; the
embedding numbers in this repository are defined for $\Gamma \le \mathcal O_v^\times$.) -/
@[kb "voight2021" "Corollary 30.5.5, p. 553"]
def LocalEmbNumFinite (F : Type) [Field F] [NumberField F] : Prop :=
  ∀ (a b : 𝓞 F), a ≠ 0 → b ≠ 0 → ∀ O : Subalgebra (𝓞 F) (QuatF F a b), IsOrder (𝓞 F) F O →
  ∀ (v : HeightOneSpectrum (𝓞 F)) (S : Type) [CommRing S] [IsDomain S] [Algebra (𝓞 F) S] [Module.Finite (𝓞 F) S],
    Module.finrank (𝓞 F) S = 2 → ∀ Γ : Subgroup (localOrder (v := v) a b O)ˣ,
      (∀ u : (localOrder (v := v) a b O)ˣ, nrd ((u : localOrder (v := v) a b O) : QuatV v a b) = 1 → u ∈ Γ) →
        Finite (Quotient (embSetoid (v.adicCompletion F)
          (S := TensorProduct (𝓞 F) (v.adicCompletionIntegers F) S) (localOrder (v := v) a b O) Γ))

/-! ### Lemma 30.6.17 (a), (b) -/

open scoped Classical in
/-- **Local embedding numbers of Eichler orders in odd residue characteristic** (Voight 2021, Lemma 30.6.17 (a) and (b)),
as a named proposition in the setting of `LocalEmbNumEichler` ($R$ a complete discrete valuation ring with finite residue
field $k$ of odd cardinality $q$, uniformizer $\pi$, $S = R[\gamma]$ with $\gamma^2 = t\gamma - n$, $d_\gamma = t^2 - 4n \ne 0$,
$f = \operatorname{ord}_{\mathfrak p}(d_\gamma)$, $e \ge 1$):
(a) if $f = 0$, then $m(S, \mathcal O_0(\pi^e); \mathcal O_0(\pi^e)^\times) = 1 + (K \mid \mathfrak p)$;
(b) if $e < f$ (i.e. $\pi^{e+1} \mid d_\gamma$), then it is $2q^{(e-1)/2}$ for $e$ odd and $q^{e/2 - 1}(q + 1)$ for $e$ even.
Parts (c) and (d) ($e = f$, $e > f > 0$) are not stated here. -/
@[kb "voight2021" "Lemma 30.6.17, p. 557"]
def LocalEmbNumEichlerOdd (R F : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field F] [Algebra R F]
    [IsFractionRing R F] (π : R) : Prop :=
  Irreducible π → IsAdicComplete (IsLocalRing.maximalIdeal R) R → Finite (IsLocalRing.ResidueField R) →
  Odd (Nat.card (IsLocalRing.ResidueField R)) →
  ∀ (S : Type) [CommRing S] [Algebra R S] (b : Module.Basis (Fin 2) R S) (t n : R), b 0 = 1 →
    b 1 * b 1 = algebraMap R S t * b 1 - algebraMap R S n → t ^ 2 - 4 * n ≠ 0 →
    ∀ e : ℕ, 1 ≤ e →
      (IsUnit (t ^ 2 - 4 * n) →
        (embNum F S (stdEichlerOrder R F π e) ⊤ : ℤ) = 1 + splitSymbol R S) ∧
      (π ^ (e + 1) ∣ t ^ 2 - 4 * n →
        embNum F S (stdEichlerOrder R F π e) ⊤ =
          if Odd e then 2 * Nat.card (IsLocalRing.ResidueField R) ^ ((e - 1) / 2)
          else Nat.card (IsLocalRing.ResidueField R) ^ (e / 2 - 1) * (Nat.card (IsLocalRing.ResidueField R) + 1))

/-! ### Proposition 30.8.5 and Main Theorem 30.8.6 -/

open scoped Classical in
/-- **Counting units by embeddings** (Voight 2021, Proposition 30.8.5), as a named proposition about a totally real number
field $F$: for a totally definite $B = (a, b)_F$ and an order $\mathcal O \subseteq B$, with $w_{\mathcal O} = [\mathcal O^\times : R^\times]$
(`ordUnitIdx`),
$$1 - \frac1{w_{\mathcal O}} = \frac12\sum_{q \ge 2}\left(1 - \frac1q\right)\sum_{[S^\times:R^\times] = q} m(S, \mathcal O; \mathcal O^\times),$$
the inner sum over the isomorphism classes of quadratic orders $S$ with $[S^\times : R^\times] = q$ (`QuadOrdCls`, `unitIdx`). -/
@[kb "voight2021" "Proposition 30.8.5, p. 561"]
def UnitCountEmb (F : Type) [Field F] [NumberField F] : Prop :=
  IsTotallyReal F → ∀ (a b : 𝓞 F), a ≠ 0 → b ≠ 0 → IsTotDefinite a b →
  ∀ O : Subalgebra (𝓞 F) (QuatF F a b), IsOrder (𝓞 F) F O →
    (1 - (ordUnitIdx O : ℝ)⁻¹) = (1 / 2) * ∑ᶠ c : QuadOrdCls F,
      if 2 ≤ unitIdx c.out then (1 - (unitIdx c.out : ℝ)⁻¹) * (embNum F c.out.1 O ⊤ : ℝ) else 0

open scoped Classical in
/-- **The Eichler class number formula** (Voight 2021, Main Theorem 30.8.6, for $R = \mathbb Z_F$ and $T$ the archimedean
places), as a named proposition about a totally real number field $F$: for a totally definite $B = (a, b)_F$ and an order
$\mathcal O \subseteq B$,
$$\#\operatorname{Cls}\mathcal O = \operatorname{mass}(\operatorname{Cls}\mathcal O) + \frac12\sum_{q \ge 2}\left(1 - \frac1q\right)
\sum_{[S^\times:R^\times] = q} h(S)\, m(\widehat S, \widehat{\mathcal O}; \widehat{\mathcal O}^\times),$$
the inner sum over the isomorphism classes of quadratic orders $S$ with $[S^\times : R^\times] = q$ whose fraction field embeds
in $B$ (the standing hypothesis of section 30.4; for the others the term is $0$), $h(S) = \#\operatorname{Pic}S$, and the adelic
embedding number $m(\widehat S, \widehat{\mathcal O}; \widehat{\mathcal O}^\times) = \prod_{\mathfrak p} m(S_{\mathfrak p}, \mathcal O_{\mathfrak p};
\mathcal O_{\mathfrak p}^\times)$ (`adelicEmbNum`; see the reading note in the module docstring). Over $\mathbb Q$ for maximal
orders this is `EichlerClassNumberFormulaMassRat`. -/
@[kb "voight2021" "Main Theorem 30.8.6, p. 562"]
def EichlerClassNumberFormula (F : Type) [Field F] [NumberField F] : Prop :=
  IsTotallyReal F → ∀ (a b : 𝓞 F), a ≠ 0 → b ≠ 0 → IsTotDefinite a b →
  ∀ O : Subalgebra (𝓞 F) (QuatF F a b), IsOrder (𝓞 F) F O →
    (clsNum O : ℝ) = clsMass O + (1 / 2) * ∑ᶠ c : QuadOrdCls F,
      if 2 ≤ unitIdx c.out ∧ ∃ φ : c.out.1 →ₐ[𝓞 F] QuatF F a b, Function.Injective φ then
        (1 - (unitIdx c.out : ℝ)⁻¹) * (quadClassNum c.out : ℝ) * (adelicEmbNum O c.out.1 : ℝ)
      else 0

/-! ### Proposition 30.9.2 (Deuring) -/

/-- Conjugacy of orders: $\mathcal O' = \alpha^{-1}\mathcal O\alpha$ for some $\alpha \in B^\times$. -/
def conjSetoid {a b : 𝓞 ℚ} : Setoid {O : Subalgebra (𝓞 ℚ) (QuatF ℚ a b) // IsMaximalOrder (𝓞 ℚ) ℚ O} where
  r O O' := ∃ α : (QuatF ℚ a b)ˣ, ∀ x, x ∈ O'.1 ↔ (α : QuatF ℚ a b) * x * ↑α⁻¹ ∈ O.1
  iseqv := by
    refine ⟨fun O => ⟨1, fun x => by simp⟩, ?_, ?_⟩
    · rintro O O' ⟨α, hα⟩
      refine ⟨α⁻¹, fun x => ?_⟩
      rw [hα (↑α⁻¹ * x * ↑α⁻¹⁻¹)]
      simp only [inv_inv, ← mul_assoc, Units.mul_inv, one_mul]
      rw [mul_assoc, Units.mul_inv, mul_one]
    · rintro O O' O'' ⟨α, hα⟩ ⟨β, hβ⟩
      refine ⟨α * β, fun x => ?_⟩
      rw [hβ, hα]
      simp only [Units.val_mul, mul_inv_rev, mul_assoc]

/-- **The type number of maximal orders** $\#\operatorname{Typ}\mathcal O$ of $B = (a, b \mid \mathbb Q)$: the number of
$B^\times$-conjugacy classes of maximal orders (Voight 2021, Definition 17.4.8; all maximal orders of $B$ lie in one genus, and
isomorphic orders are conjugate by Skolem–Noether). -/
@[kb "voight2021" "Definition 17.4.8, p. 282"]
def typNumMax (a b : 𝓞 ℚ) : ℕ := Nat.card (Quotient (conjSetoid (a := a) (b := b)))

/-- **Deuring's type number formula** (Voight 2021, Proposition 30.9.2), as a named proposition: let $B = (a, b \mid \mathbb Q)$
be definite of prime discriminant $p$ and $\mathcal O \subset B$ a maximal order. Then $\#\operatorname{Typ}\mathcal O = 1$ for
$p = 2, 3$, and for $p \ge 5$
$$\#\operatorname{Typ}\mathcal O = \frac12\#\operatorname{Cls}\mathcal O + \frac14\bigl([h(-p)] + h(-4p)\bigr),$$
where $h(\Delta)$ is the class number of the imaginary quadratic order of discriminant $\Delta$ (`formClassNumber`) and
$[h(-p)] = h(-p)$ if $p \equiv 3 \pmod 4$ and $0$ otherwise. -/
@[kb "voight2021" "Proposition 30.9.2, p. 563"]
def DeuringTypeNumber : Prop :=
  ∀ (a b : 𝓞 ℚ) (ha : a ≠ 0) (hb : b ≠ 0), IsTotDefinite a b → ∀ p : ℕ, p.Prime →
    ∏ v ∈ ramFin ha hb, Ideal.absNorm v.asIdeal = p →
    ∀ O : Subalgebra (𝓞 ℚ) (QuatF ℚ a b), IsMaximalOrder (𝓞 ℚ) ℚ O →
      (typNumMax a b : ℝ) =
        if p ≤ 3 then 1
        else (clsNum O : ℝ) / 2 +
          ((if p % 4 = 3 then (formClassNumber (-(p : ℤ)) : ℝ) else 0) + formClassNumber (-4 * (p : ℤ))) / 4

/-! ### Corollary 30.4.18 (proved from the trace formula) -/

section Genus

variable {F : Type} [Field F] [NumberField F]

/-- A finite product of nonzero natural numbers (`finprod`) is nonzero. -/
theorem finprod_ne_zero_nat {ι : Type*} {f : ι → ℕ} (hf : ∀ i, f i ≠ 0) : ∏ᶠ i, f i ≠ 0 := by
  by_cases h : (Function.mulSupport f).Finite
  · rw [finprod_eq_prod f h]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hf i
  · rw [finprod_of_infinite_mulSupport h]; exact one_ne_zero

/-- **Local optimal embeddings glue to some order in the genus** (Voight 2021, Corollary 30.4.18), **proved conditional on
the trace formula** `TraceFormulaEmb F` (Theorem 30.4.7, stated in wave 4): let $\mathcal O \subseteq (a, b)_F$ be an order and
$S$ a quadratic $\mathbb Z_F$-order that is a domain, whose fraction field embeds in $B$, with finite class group. If
$\operatorname{Emb}(S_{\mathfrak p}, \mathcal O_{\mathfrak p}) \ne \emptyset$ for every prime $\mathfrak p$, then for some class
$[J] \in \operatorname{Cls}\mathcal O$ the order $\mathcal O_R(J)$ (which lies in the genus of $\mathcal O$) admits an optimal
embedding of $S$. The finiteness of $\operatorname{Pic}S$ is assumed (it holds for every order in a number field, but Mathlib
proves it only for rings of integers). -/
@[kb "voight2021" "Corollary 30.4.18, p. 550"]
theorem exists_embNum_ne_zero (hT : TraceFormulaEmb F) {a b : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0)
    {O : Subalgebra (𝓞 F) (QuatF F a b)} (hO : IsOrder (𝓞 F) F O)
    (S : Type) [CommRing S] [IsDomain S] [Algebra (𝓞 F) S] [Module.Finite (𝓞 F) S] (hS : Module.finrank (𝓞 F) S = 2)
    (hemb : ∃ φ : S →ₐ[𝓞 F] QuatF F a b, Function.Injective φ) [Finite (ClassGroup S)]
    (hloc : ∀ v : HeightOneSpectrum (𝓞 F),
      embNum (v.adicCompletion F) (TensorProduct (𝓞 F) (v.adicCompletionIntegers F) S) (localOrder (v := v) a b O) ⊤ ≠ 0) :
    ∃ c : ClsO O, embNum F S (rightOrder c.1.out) ⊤ ≠ 0 := by
  have h := hT a b ha hb O hO S hS hemb
  have hrhs : Nat.card (ClassGroup S) * ∏ᶠ v : HeightOneSpectrum (𝓞 F),
      embNum (v.adicCompletion F) (TensorProduct (𝓞 F) (v.adicCompletionIntegers F) S)
        (localOrder (v := v) a b O) ⊤ ≠ 0 :=
    mul_ne_zero (Nat.card_pos (α := ClassGroup S)).ne' (finprod_ne_zero_nat hloc)
  rw [← h] at hrhs
  by_contra hne
  push Not at hne
  exact hrhs (finsum_eq_zero_of_forall_eq_zero hne)

end Genus

end QuadFormsKB.Voight.Wave5
