/-
# Genus, type set and the finiteness of class sets; Eichler orders over $\mathbb Q$: statements (Voight, 17.4.8, 17.7.1, 28.2.11)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021 (key `voight2021`): Definition 17.4.8 (p. 282),
Main Theorem 17.7.1 (p. 287), Theorem 28.2.11 (p. 481).

**Setting.** $F$ a number field, $R = \mathbb Z_F$ (the book's $R(S)$ for $S$ the archimedean places, which is eligible),
$B = (a, b)_F$ = `QuatF F a b`, orders `Subalgebra (𝓞 F) (QuatF F a b)` with `IsOrder`. Two orders are **locally
isomorphic** if their completions $\mathcal O_{\mathfrak p}, \mathcal O'_{\mathfrak p}$ (`localOrder`) are isomorphic
$R_{\mathfrak p}$-algebras for every prime $\mathfrak p$. Class sets are `ClsO` (locally principal left ideals).

**Contents.**
* `IsLocIso`, `Gen`, `Typ` (**Definition 17.4.8**): the genus of $\mathcal O$ (orders of $B$ locally isomorphic to $\mathcal O$)
  and its type set (the genus modulo isomorphism of $R$-algebras). Definitions.
* `ClassTypeFinite F` (**Main Theorem 17.7.1**, $R = \mathbb Z_F$): $\operatorname{Cls}\mathcal O$ and $\operatorname{Typ}\mathcal O$ are
  finite for every order. Named proposition, not proved here (the class set of a maximal order in a definite algebra is
  proved finite: `QuatOrder.Gen.finite_classes`).
* `EichlerOrderIndefiniteRat` (**Theorem 28.2.11**): an Eichler order $\mathcal O$ in an indefinite quaternion algebra over
  $\mathbb Q$ has $\#\operatorname{Cls}\mathcal O = 1$, $\#\operatorname{Typ}\mathcal O = 1$, and $\mathcal O^1 \to (\mathcal O/m\mathcal O)^1$ is
  surjective for every $m$. Named proposition, not proved here (it needs strong approximation, Main Theorem 28.5.3).
  For maximal orders, (a) is `Voight.ClassNumberOneIndefiniteRat`.
-/
import QuadFormsKB.Literature.Voight.Wave2.Statements

open NumberField IsDedekindDomain Quaternion

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Voight.Wave6

open QuadFormsKB.Quat QuadFormsKB.QuatOrder QuadFormsKB.Voight

variable {F : Type} [Field F] [NumberField F]

/-- **Locally isomorphic orders** (Voight 2021, Definition 17.4.8): $\mathcal O_{\mathfrak p} \cong \mathcal O'_{\mathfrak p}$ as
$R_{\mathfrak p}$-algebras for every prime $\mathfrak p$ (completions `localOrder`). -/
@[kb "voight2021" "Definition 17.4.8, p. 282"]
def IsLocIso {a b : 𝓞 F} (O O' : Subalgebra (𝓞 F) (QuatF F a b)) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F),
    Nonempty (localOrder (v := v) a b O ≃ₐ[v.adicCompletionIntegers F] localOrder (v := v) a b O')

/-- **The genus** $\operatorname{Gen}\mathcal O$ (Voight 2021, Definition 17.4.8): the orders of $B$ locally isomorphic to
$\mathcal O$. -/
@[kb "voight2021" "Definition 17.4.8, p. 282"]
def Gen {a b : 𝓞 F} (O : Subalgebra (𝓞 F) (QuatF F a b)) : Type :=
  {O' : Subalgebra (𝓞 F) (QuatF F a b) // IsOrder (𝓞 F) F O' ∧ IsLocIso O O'}

/-- Isomorphism of $R$-algebras, on the genus. -/
def genSetoid {a b : 𝓞 F} (O : Subalgebra (𝓞 F) (QuatF F a b)) : Setoid (Gen O) where
  r O₁ O₂ := Nonempty (O₁.1 ≃ₐ[𝓞 F] O₂.1)
  iseqv := ⟨fun _ => ⟨AlgEquiv.refl⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

/-- **The type set** $\operatorname{Typ}\mathcal O$ (Voight 2021, Definition 17.4.8): the isomorphism classes of orders in the
genus of $\mathcal O$. (By Skolem–Noether, isomorphic orders of $B$ are conjugate by $B^\times$; for maximal orders over
$\mathbb Q$ compare `Wave5.typNumMax`.) -/
@[kb "voight2021" "Definition 17.4.8, p. 282"]
def Typ {a b : 𝓞 F} (O : Subalgebra (𝓞 F) (QuatF F a b)) : Type := Quotient (genSetoid O)

/-- **Finiteness of the class set and the type set** (Voight 2021, Main Theorem 17.7.1 with $R = \mathbb Z_F$), as a named
proposition about the number field $F$: for every quaternion algebra $B = (a, b)_F$ and every order $\mathcal O \subseteq B$,
$\operatorname{Cls}\mathcal O$ (`ClsO`) and $\operatorname{Typ}\mathcal O$ (`Typ`) are finite. -/
@[kb "voight2021" "Main Theorem 17.7.1, p. 287"]
def ClassTypeFinite (F : Type) [Field F] [NumberField F] : Prop :=
  ∀ (a b : 𝓞 F), a ≠ 0 → b ≠ 0 → ∀ O : Subalgebra (𝓞 F) (QuatF F a b), IsOrder (𝓞 F) F O →
    Finite (ClsO O) ∧ Finite (Typ O)

/-- **Eichler orders in indefinite algebras over $\mathbb Q$** (Voight 2021, Theorem 28.2.11), as a named proposition: let
$B = (a, b)_{\mathbb Q}$ be indefinite ($a > 0$ or $b > 0$) and $\mathcal O \subseteq B$ an Eichler order (`IsEichlerOrder`). Then
(a) $\#\operatorname{Cls}\mathcal O = 1$; (b) $\#\operatorname{Typ}\mathcal O = 1$; (c) for every integer $m \ne 0$ the reduction map
$\mathcal O^1 \to (\mathcal O/m\mathcal O)^1$ is surjective, written elementwise: every $x \in \mathcal O$ with
$\operatorname{nrd}(x) \equiv 1 \pmod m$ is congruent modulo $m\mathcal O$ to some $\gamma \in \mathcal O$ with $\operatorname{nrd}(\gamma) = 1$.
(For $m = 0$ the statement is trivial in the book's form; $m \ne 0$ is assumed.) -/
@[kb "voight2021" "Theorem 28.2.11, p. 481"]
def EichlerOrderIndefiniteRat : Prop :=
  ∀ (a b : 𝓞 ℚ), a ≠ 0 → b ≠ 0 → (0 < (a : ℚ) ∨ 0 < (b : ℚ)) →
    ∀ O : Subalgebra (𝓞 ℚ) (QuatF ℚ a b), IsEichlerOrder O →
      clsNum O = 1 ∧ Nat.card (Typ O) = 1 ∧
      ∀ m : 𝓞 ℚ, m ≠ 0 → ∀ x ∈ O, (∃ r : 𝓞 ℚ, nrd x = 1 + algebraMap (𝓞 ℚ) ℚ (m * r)) →
        ∃ γ ∈ O, nrd γ = 1 ∧ ∃ y ∈ O, γ = x + algebraMap (𝓞 ℚ) (QuatF ℚ a b) m * y

/-! ### Lemma 30.8.2: maximal cyclic subgroups of $\mathcal O^\times/R^\times$ -/

/-- The image of $R^\times$ in $\mathcal O^\times$ (central scalars). -/
def scalarUnitsO {a b : 𝓞 F} (O : Subalgebra (𝓞 F) (QuatF F a b)) : Subgroup Oˣ :=
  (Units.map (algebraMap (𝓞 F) O : 𝓞 F →* O)).range

instance scalarUnitsO_normal {a b : 𝓞 F} (O : Subalgebra (𝓞 F) (QuatF F a b)) : (scalarUnitsO O).Normal :=
  ⟨by
    rintro _ ⟨r, rfl⟩ g
    refine ⟨r, Units.ext ?_⟩
    simp only [Units.coe_map, MonoidHom.coe_coe, Units.val_mul]
    rw [← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]⟩

/-- **Maximal cyclic subgroups** (Voight 2021, Lemma 30.8.2), as a named proposition about a totally real number field $F$:
for $B = (a, b)_F$ totally definite and an order $\mathcal O \subseteq B$, every nontrivial element of the (finite) group
$\mathcal O^\times/R^\times$ lies in a unique maximal cyclic subgroup (a cyclic subgroup not properly contained in another cyclic
subgroup). -/
@[kb "voight2021" "Lemma 30.8.2, p. 561"]
def UniqueMaxCyclic (F : Type) [Field F] [NumberField F] : Prop :=
  IsTotallyReal F → ∀ (a b : 𝓞 F), a ≠ 0 → b ≠ 0 → IsTotDefinite a b →
  ∀ O : Subalgebra (𝓞 F) (QuatF F a b), IsOrder (𝓞 F) F O →
    ∀ g : Oˣ ⧸ scalarUnitsO O, g ≠ 1 →
      ∃! C : Subgroup (Oˣ ⧸ scalarUnitsO O), g ∈ C ∧ IsCyclic C ∧
        ∀ C' : Subgroup (Oˣ ⧸ scalarUnitsO O), IsCyclic C' → C ≤ C' → C' = C

end QuadFormsKB.Voight.Wave6
