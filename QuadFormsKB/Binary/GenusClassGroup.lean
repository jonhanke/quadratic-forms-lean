import QuadFormsKB.Binary.GenusCount

/-!
# Every genus has $h/2^{t-1}$ classes, through an interface for Gauss composition

Gauss composition makes the proper ($\mathrm{SL}_2(\mathbb{Z})$-) classes of primitive positive definite forms of
discriminant $D$ into a finite abelian group $\mathrm{Cl}(D)$ of order $h(D)$; for fundamental $D$ it is the ideal
class group of $\mathbb{Q}(\sqrt D)$. That identification (forms ↔ ideals) is made in `GenusComposition.lean`;
this file states what the genus theory needs from it as a named **interface** (`IsFormClassGroup`) and proves the genus-theory
consequences from it:

* the genus characters give a homomorphism $\gamma : \mathrm{Cl}(D) \to \{\pm 1\}^t$ (`genusHom`) whose image is the
  product-one subgroup (`range_genusHom`, by `generaVec_bijective`);
* **every genus contains the same number of classes, $h(D)/2^{t-1}$** (`card_classes_in_genus`): the classes in a
  genus are a coset of $\ker\gamma$, the **principal genus**;
* **squares lie in the principal genus** (`genusHom_sq`), i.e. $\mathrm{Cl}(D)^2 \subseteq \ker\gamma$.

The reverse inclusion $\ker\gamma \subseteq \mathrm{Cl}(D)^2$ (Gauss's duplication theorem, *Disq. Arith.* §286;
Cox, Theorem 3.15 / Corollary 3.14) is not proved here; it needs the count of ambiguous classes
($|\mathrm{Cl}(D)[2]| = 2^{t-1}$), which needs composition itself.

*Update:* the interface is discharged for $G = \mathrm{Cl}(\mathcal O_{K_D})$ in `GenusComposition.lean`
(`isFormClassGroup`), so the class count holds unconditionally (`card_classes_in_genus'`), and the duplication
theorem $\ker\gamma = \mathrm{Cl}^2$ with $|\mathrm{Cl}[2]| = 2^{t-1}$ is proved in `GenusDuplication.lean`
(`principalGenus_eq_sq`, `card_twoTorsion`).

The interface fields of `IsFormClassGroup` are exactly the facts used: (for a commutative group $G$, finite in the count, and a class map) a surjective class map from
`PosForms D`, classes lying inside genera (proper equivalence implies $\mathbb{Z}_p$- and $\mathbb{R}$-equivalence),
and multiplicativity of the genus characters under composition (Cox, Lemma 3.17 and Theorem 3.15's proof: if
$f$ and $g$ represent $m$ and $m'$ prime to $D$, their composite represents $mm'$).

Sources: Gauss, *Disq. Arith.* §§234–260 (composition), §§247, 252 (each genus has the same number of classes),
§286; Cox, §3.B and Theorem 3.15; Buell, Ch. 4, Theorem 4.2.
-/

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Binary

open BinQF Siegel

variable {D : ℤ}

/-- **Interface: Gauss composition on the proper classes of primitive positive definite forms of discriminant $D$**
(to be supplied by forms ↔ ideals; for fundamental $D$, $\mathrm{Cl}(D) \cong$ the ideal class group).
The data are a commutative group $G = \mathrm{Cl}(D)$ (finite in the theorems; $h(D) = |G|$) and the class map
$\mathrm{cls} : $ `PosForms D` $\to G$, $f \mapsto [f]$; this proposition says they behave like composition.

Fields:
- `cls_surjective`: every class contains a primitive positive definite form of discriminant $D$;
- `sameGenus_of_cls_eq`: forms in the same class are in the same genus (`Siegel.SameGenus`);
- `genusVec_mul`: the genus characters are multiplicative: if $[h] = [f][g]$ then $\chi_p(h) = \chi_p(f)\chi_p(g)$
  for all $p \mid D$.

*Classification:* an interface, not a cited theorem: the axioms of composition that the genus theory uses. It
is not equivalent to the conclusions drawn from it (the class count needs the genus theory on top). -/
@[kb "cox2013" "§3.A–B, Thm. 3.9 and Lemma 3.17 (interface) [unverified]"]
structure IsFormClassGroup (D : ℤ) (G : Type*) [CommGroup G] (cls : PosForms D → G) : Prop where
  /-- Every class contains a primitive positive definite form. -/
  cls_surjective : Function.Surjective cls
  /-- Forms in the same class lie in the same genus. -/
  sameGenus_of_cls_eq : ∀ f g : PosForms D, cls f = cls g → SameGenus f.1 g.1
  /-- The genus characters are multiplicative under composition. -/
  genusVec_mul : ∀ f g h : PosForms D, cls h = cls f * cls g →
    genusVec D h.1 = genusVec D f.1 * genusVec D g.1

namespace IsFormClassGroup

variable {G : Type*} [CommGroup G] {cls : PosForms D → G} (C : IsFormClassGroup D G cls)
include C

/-- A chosen form in a class. -/
noncomputable def rep (x : G) : PosForms D := (C.cls_surjective x).choose

theorem cls_rep (x : G) : cls (C.rep x) = x := (C.cls_surjective x).choose_spec

/-- Forms in the same class have the same genus vector. -/
theorem genusVec_eq_of_cls_eq [IsQuadDisc D] {f g : PosForms D} (h : cls f = cls g) :
    genusVec D f.1 = genusVec D g.1 :=
  (sameGenus_iff_genusVec_eq f.2.1 g.2.1 f.2.2.1 g.2.2.1 f.2.2.2 g.2.2.2).mp (C.sameGenus_of_cls_eq f g h)

/-- **The genus homomorphism** $\gamma : \mathrm{Cl}(D) \to \{\pm 1\}^t$, $[f] \mapsto (\chi_p(f))_{p \mid D}$. -/
noncomputable def genusHom [IsQuadDisc D] : G →* (D.natAbs.primeFactors → ℤˣ) where
  toFun x := genusVec D (C.rep x).1
  map_one' := by
    have h := C.genusVec_mul (C.rep 1) (C.rep 1) (C.rep 1) (by rw [C.cls_rep, mul_one])
    have : genusVec D (C.rep 1).1 * genusVec D (C.rep 1).1 = genusVec D (C.rep 1).1 * 1 := by
      rw [← h, mul_one]
    exact mul_left_cancel this
  map_mul' x y := (C.genusVec_mul (C.rep x) (C.rep y) (C.rep (x * y)) (by rw [C.cls_rep, C.cls_rep, C.cls_rep])).trans
    rfl

/-- $\gamma([f]) = (\chi_p(f))_p$. -/
theorem genusHom_cls [IsQuadDisc D] (f : PosForms D) : C.genusHom (cls f) = genusVec D f.1 :=
  C.genusVec_eq_of_cls_eq (C.cls_rep (cls f))

/-- **Squares lie in the principal genus:** $\gamma(x^2) = 1$ ($\gamma$ takes values in $\{\pm 1\}^t$). -/
@[kb "gauss1801" "§247 [unverified]"]
theorem genusHom_sq [IsQuadDisc D] (x : G) : C.genusHom (x ^ 2) = 1 := by
  rw [map_pow]
  funext p
  rcases Int.units_eq_one_or (C.genusHom x p) with h | h <;> simp [h]

/-- **The image of $\gamma$ is the product-one subgroup** of $\{\pm 1\}^t$ (`prod_genusVec` and
`generaVec_bijective`). -/
theorem mem_range_genusHom_iff [IsQuadDisc D] (hD : D < 0) (e : D.natAbs.primeFactors → ℤˣ) :
    e ∈ C.genusHom.range ↔ ∏ p, e p = 1 := by
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨f, rfl⟩ := C.cls_surjective x
    rw [genusHom_cls]
    exact prod_genusVec f.2.1 f.2.2.1 f.2.2.2
  · intro he
    obtain ⟨𝒢, h𝒢⟩ := (generaVec_bijective hD).2 ⟨e, he⟩
    induction 𝒢 using Quotient.inductionOn with | h f => ?_
    refine ⟨cls f, ?_⟩
    rw [genusHom_cls]
    exact congrArg Subtype.val h𝒢

/-- **$|\gamma(\mathrm{Cl}(D))| = 2^{t-1}$.** -/
theorem card_range_genusHom [IsQuadDisc D] (hD : D < 0) :
    Nat.card C.genusHom.range = 2 ^ (D.natAbs.primeFactors.card - 1) := by
  have hne : (D.natAbs.primeFactors).Nonempty :=
    Nat.nonempty_primeFactors.mpr (by have := three_le_natAbs (D := D); omega)
  have : Nonempty D.natAbs.primeFactors := hne.coe_sort
  rw [← Fintype.card_coe D.natAbs.primeFactors, ← card_signVec_prod_one]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun e => C.mem_range_genusHom_iff hD e)

/-- **The genus of a class** (in `Genera D`). -/
noncomputable def genusOf (x : G) : Genera D := Quotient.mk (genusSetoid D) (C.rep x)

/-- A class lies in the genus $\mathcal G$ iff its genus vector is that of $\mathcal G$. -/
theorem genusOf_eq_iff [IsQuadDisc D] (hD : D < 0) (x : G) (𝒢 : Genera D) :
    C.genusOf x = 𝒢 ↔ C.genusHom x = (generaVec 𝒢).1 := by
  rw [← (generaVec_bijective hD).1.eq_iff]
  constructor
  · intro h; rw [← h]; rfl
  · intro h; exact Subtype.ext h

/-- **Every genus has the same number of classes, $h(D)/2^{t-1}$** (Gauss, *Disq. Arith.* §252; Cox, Theorem 3.15;
Buell, Theorem 4.2), from the interface `IsFormClassGroup` (composition) and the genus theory: for a
fundamental $D < 0$ with $t$ prime factors and every genus $\mathcal G$,
$$\#\{x \in \mathrm{Cl}(D) : x \in \mathcal G\} \cdot 2^{t-1} = h(D) = |\mathrm{Cl}(D)| .$$
The classes in $\mathcal G$ are a coset of $\ker\gamma$, and $|\mathrm{Cl}(D)| = |\ker\gamma| \cdot |\gamma(\mathrm{Cl}(D))|$
with $|\gamma(\mathrm{Cl}(D))| = 2^{t-1}$ (`card_range_genusHom`). -/
@[kb "gauss1801" "§252 [unverified]"]
theorem card_classes_in_genus [IsQuadDisc D] [Finite G] (hD : D < 0) (𝒢 : Genera D) :
    Nat.card {x : G // C.genusOf x = 𝒢} * 2 ^ (D.natAbs.primeFactors.card - 1) = Nat.card G := by
  -- `𝒢` is the genus of some class `x₀`
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : G, C.genusHom x₀ = (generaVec 𝒢).1 :=
    (C.mem_range_genusHom_iff hD _).mpr (generaVec 𝒢).2
  -- the fibre over `γ(x₀)` is the coset `x₀ ker γ`
  have hfib : Nat.card {x : G // C.genusOf x = 𝒢} = Nat.card C.genusHom.ker := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x₀⁻¹ * x.1, by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hx₀, ← (C.genusOf_eq_iff hD _ _).mp x.2, inv_mul_cancel]⟩
        invFun := fun y => ⟨x₀ * y.1, by
          rw [C.genusOf_eq_iff hD, map_mul, MonoidHom.mem_ker.mp y.2, mul_one, hx₀]⟩
        left_inv := fun x => by simp
        right_inv := fun y => by simp }
  rw [hfib, ← C.card_range_genusHom hD, ← Subgroup.index_ker, Subgroup.card_mul_index]

end IsFormClassGroup

end QuadFormsKB.Binary
