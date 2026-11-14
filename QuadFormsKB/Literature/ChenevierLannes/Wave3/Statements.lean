/-
# Chenevier–Lannes, §2.3 and §3.4.2: Niemeier's classification in root-system form; Weyl vectors and the holy
# constructions of the Leech lattice

Source: Chenevier–Lannes 2019 (`chenevierlannes2019`), §1.1, p. 2; §1.2, p. 5 ((1.2.1)); §2.3, Proposition-Definition
2.3.3, p. 35, Theorem 2.3.17, p. 43; §3.1, Proposition 3.1.4 and the algorithm after Proposition 3.1.5, pp. 47–48;
§3.4.2, pp. 65–70 (Weyl vectors, Proposition 3.4.2.1, Theorem 3.4.2.10). Printed page numbers.

**Layer.** `ADETable.lean` (types of root systems, Table 1.1 and its completeness), `Roots.lean`, and the root lattice
$Q(R(L))$ = `rootLattice Q`. The isomorphism type of the root system $R(L)$ is recorded through the root
lattice: "$R(L)$ is of type $R$" (`HasRootType Q R`) means that $(\mathbb{Z}R(L), q_L)$ is isometric to the root lattice
$Q(R)$ of $R$, the orthogonal sum of the lattices with Gram matrix the Cartan matrix of each component (`rootFormList`,
Mathlib's `CartanMatrix.A`, `CartanMatrix.D`, `CartanMatrix.E`). *Deviation (equivalent reformulation):* the book
speaks of isomorphisms of root systems; for root systems of type ADE these are the same as isometries of the root
lattices (the roots of $Q(R)$ are exactly $R$, and $R$ generates $Q(R)$; Bourbaki, Chap. VI, §4), a fact not
formalized here.

**States** (named propositions, not proved; the book's proofs use Venkov's harmonic theta series, the classification of
root systems, Conway's theorem and a case-by-case study of the Lagrangians of the Venkov modules):
- `EquiCoxeterRootSystem n` (Proposition-Definition 2.3.3 (a)–(c), $n = 8, 16, 24$): a nonempty $R(L)$ is a root system
  of type ADE, of rank $n$, equi-Coxeter with Coxeter number $h(L) = |R(L)|/n$;
- `NiemeierClassification` (Theorem 2.3.17, with 1.1.r6 of §1.1): $L \mapsto R(L)$ is a bijection from $X_{24}$ onto the
  set made of $\emptyset$ and the $23$ root systems of Table 1.1;
- `IsWeylVector`, `WeylVectorIntegral` (Proposition 3.4.2.1, Borcherds): Weyl vectors of a Niemeier lattice lie in $L$;
- `HolyConstructions` (Theorem 3.4.2.10 (a), (c); (1.2.1), p. 5): for a Weyl vector $\rho$ and $d \in \{h, h + 1\}$,
  $\rho$ defines a point of the quadric $C_L(\mathbb{Z}/d)$, and $\mathrm{vois}_d(L; \rho) \cong \mathrm{Leech}$.

**Proves:**
- `rootType_mem_table` (**conditional** on `EquiCoxeterRootSystem 24`): the root system of a Niemeier lattice with roots
  is one of the $23$ of Table 1.1, with $h(L)$ its Coxeter number (from the completeness of Table 1.1, unconditional);
- `classSet_ncard_of_classification` (**conditional** on `NiemeierClassification`): $|X_{24}| = 24$;
- `conwayLeechUnique_of_classification`, `leechExists_of_classification` (**conditional** on `NiemeierClassification`):
  Conway's theorem and the existence of the Leech lattice are part of Theorem 2.3.17.
-/
import QuadFormsKB.Literature.ChenevierLannes.Wave3.ADETable
import QuadFormsKB.Literature.ChenevierLannes.Wave3.Roots
import QuadFormsKB.Witt.Bridge

open Matrix

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Siegel QuadFormsKB.Siegel.Kneser ADEType

variable {n : ℕ}

/-! ### Root lattices of the ADE types -/

/-- **The Cartan matrix of an irreducible type** (Mathlib's `CartanMatrix.A m`, `CartanMatrix.D m`,
`CartanMatrix.E 6`, `E 7`, `E 8`): the Gram matrix $(\alpha_i \cdot \alpha_j)$ of a basis of simple roots. -/
def ADEType.cartan : (t : ADEType) → Matrix (Fin t.rank) (Fin t.rank) ℤ
  | A m => CartanMatrix.A m
  | D m => CartanMatrix.D m
  | E6 => CartanMatrix.E 6
  | E7 => CartanMatrix.E 7
  | E8 => CartanMatrix.E 8

/-- **The root lattice $Q(t)$ of an irreducible type** as an integral form: $q(x) = \tfrac12 x^{\mathsf T}Cx$ with $C$
the Cartan matrix (diagonal entries $2$, so $q$ has diagonal coefficients $1$ and off-diagonal coefficients
$C_{ij}$, $i < j$; the same construction as `Siegel.e8`). -/
def ADEType.rootForm (t : ADEType) : QuadForm ℤ t.rank :=
  QuadForm.ofUpper fun i j => if i = j then 1 else t.cartan i j

/-- **The root lattice $Q(R)$ of a root system $R = t_1 \oplus \cdots \oplus t_k$** given as a list of types: the
orthogonal sum $Q(t_1) \perp \cdots \perp Q(t_k)$, of dimension $\sum_i \operatorname{rank}(t_i)$. -/
def rootFormList : (T : List ADEType) → QuadForm ℤ (T.map ADEType.rank).sum
  | [] => QuadForm.ofUpper fun _ _ => 0
  | t :: T => QuadForm.orthSum t.rootForm (rootFormList T)

/-- **$Q(R(L))$ is isometric to the root lattice of $T$**: a $\mathbb{Z}$-linear bijection $f$ from
$\mathbb{Z}^{\operatorname{rank} T}$ onto the root lattice $\mathbb{Z}R(L)$ (`rootLattice Q`) with
$q_L(f(x)) = q_T(x)$. -/
def IsRootLatticeOfType (Q : QuadForm ℤ n) (T : List ADEType) : Prop :=
  ∃ f : (Fin (T.map ADEType.rank).sum → ℤ) ≃ₗ[ℤ] rootLattice Q,
    ∀ x, Q.eval (f x : Fin n → ℤ) = (rootFormList T).eval x

/-- **"$R(L)$ is a root system of type $R$"** ($R$ a multiset of irreducible types): for some ordering $T$ of the
components, $Q(R(L)) \cong Q(T)$ (`IsRootLatticeOfType`). -/
@[kb "chenevierlannes2019" "§2.3, p. 34 (R(L) of a given type, via the root lattice)"]
def HasRootType (Q : QuadForm ℤ n) (R : Multiset ADEType) : Prop :=
  ∃ T : List ADEType, (T : Multiset ADEType) = R ∧ IsRootLatticeOfType Q T

/-! ### Proposition-Definition 2.3.3 and Theorem 2.3.17 -/

/-- **Proposition-Definition 2.3.3** (Chenevier–Lannes, p. 35; Venkov; named statement for one $n \in \{8, 16, 24\}$):
if an even unimodular lattice $L$ of dimension $n$ has roots, then (a) $R(L)$ is a root system of type ADE and rank
$n$, (b) all its irreducible components have the same Coxeter number $h$, and (c) $|R(L)| = nh$, i.e. $h = h(L)$
(`coxeterNumber Q = |R(L)|/n`). The rank part of (a) is proved conditional on Venkov's identity
(`eq_zero_of_orthogonal_roots`); the ADE-type statement needs the classification of root systems. -/
@[kb "chenevierlannes2019" "Prop.-Def. 2.3.3, p. 35"]
def EquiCoxeterRootSystem (n : ℕ) : Prop :=
  ∀ Q : QuadForm ℤ n, IsEvenUnimodular Q → (rootSet Q).Nonempty →
    ∃ (R : Multiset ADEType) (h : ℕ), R ≠ 0 ∧ IsADE R ∧ adeRank R = n ∧ IsEquiCoxeter R h ∧ HasRootType Q R ∧
      coxeterNumber Q = h

/-- **The root system of a Niemeier lattice with roots is in Table 1.1** (Chenevier–Lannes, p. 36): **conditional** on
`EquiCoxeterRootSystem 24`; then the completeness of Table 1.1 (`mem_niemeierRootTable_of_equiCoxeter`, unconditional)
places $R(L)$ among the $23$ entries, and $h(L)$ is the entry's Coxeter number. -/
@[kb "chenevierlannes2019" "p. 36 (R(L) is one of R_1, ..., R_23; conditional)"]
theorem rootType_mem_table (hE : EquiCoxeterRootSystem 24) {Q : QuadForm ℤ 24} (hQ : IsNiemeier Q)
    (hR : (rootSet Q).Nonempty) :
    ∃ e ∈ niemeierRootTable, HasRootType Q e.1 ∧ coxeterNumber Q = e.2 := by
  obtain ⟨R, h, hR0, hADE, hrank, heq, htype, hcox⟩ := hE Q hQ hR
  exact ⟨(R, h), mem_niemeierRootTable_of_equiCoxeter hR0 hADE hrank heq, htype, hcox⟩

/-- The $i$-th root system of Table 1.1 ($R_{i+1}$ in the book's numbering, p. 36). -/
def tableRoot (i : Fin 23) : Multiset ADEType :=
  (niemeierRootTable.get (i.cast niemeierRootTable_length.symm)).1

/-- **Theorem 2.3.17 (Niemeier)** (Chenevier–Lannes, p. 43; §1.1, p. 2; named statement): the map $L \mapsto R(L)$
induces a bijection from $X_{24}$ onto the set of $24$ elements made of the empty root system and the $23$ equi-Coxeter
root systems of type ADE and rank $24$ (Table 1.1). Formally: there is a map $\tau : X_{24} \to \{\emptyset\} \sqcup
\{R_1, \dots, R_{23}\}$ (`Option (Fin 23)`, `none` for $\emptyset$), bijective from $X_{24}$, such that for every
Niemeier lattice $L$, $\tau([L]) = \emptyset$ iff $R(L) = \emptyset$, and $\tau([L]) = R_i$ implies that $R(L)$ is of
type $R_i$ (`HasRootType`). -/
@[kb "chenevierlannes2019" "Thm. 2.3.17, p. 43; §1.1, p. 2"]
def NiemeierClassification : Prop :=
  ∃ τ : QClass 24 → Option (Fin 23), Set.BijOn τ (classSet 24) Set.univ ∧
    ∀ Q : QuadForm ℤ 24, IsNiemeier Q →
      (τ (classOf Q) = none ↔ rootSet Q = ∅) ∧ ∀ i : Fin 23, τ (classOf Q) = some i → HasRootType Q (tableRoot i)

/-- **$|X_{24}| = 24$** (Chenevier–Lannes, §1.1, p. 2): **conditional** on `NiemeierClassification`. -/
@[kb "chenevierlannes2019" "§1.1, p. 2 (|X_24| = 24, from Thm. 2.3.17)"]
theorem classSet_ncard_of_classification (h : NiemeierClassification) : (classSet 24).ncard = 24 := by
  obtain ⟨τ, hbij, -⟩ := h
  rw [hbij.ncard_eq, Set.ncard_univ]
  simp

/-- **Conway's theorem is part of Theorem 2.3.17** (Theorem 2.3.16, p. 43): **conditional** on
`NiemeierClassification`. -/
theorem conwayLeechUnique_of_classification (h : NiemeierClassification) : ConwayLeechUnique := by
  intro M M' hM hM'
  obtain ⟨τ, hbij, hτ⟩ := h
  have e1 := (hτ M hM.1).1.mpr hM.2
  have e2 := (hτ M' hM'.1).1.mpr hM'.2
  have := hbij.injOn (mem_classSet_classOf.mpr hM.1) (mem_classSet_classOf.mpr hM'.1) (e1.trans e2.symm)
  exact classOf_eq_classOf_iff.mp this

/-- **The Leech lattice exists** (§1.1, p. 2): **conditional** on `NiemeierClassification` (surjectivity onto
$\emptyset$). -/
theorem leechExists_of_classification (h : NiemeierClassification) : LeechExists := by
  obtain ⟨τ, hbij, hτ⟩ := h
  obtain ⟨x, hx, hxτ⟩ := hbij.surjOn (Set.mem_univ none)
  obtain ⟨Q, hQ, rfl⟩ := hx
  exact ⟨Q, hQ, (hτ Q hQ).1.mp hxτ⟩

/-! ### Weyl vectors and the holy constructions -/

/-- **A Weyl vector** of a lattice with roots (Chenevier–Lannes, §3.4.2, p. 65): $\rho \in \mathbb{Q} \otimes L$ with
$2\rho = \sum_{\alpha \in R^+} \alpha$ for the positive roots $R^+ = \{\alpha \in R(L) : \alpha \cdot \xi > 0\}$ of a
chamber, i.e. for some $\xi \in \mathbb{Q}^n$ orthogonal to no root. (The book takes $\xi$ in a chamber
$C \subset \mathbb{R} \otimes L$; every chamber is an open cone, so it contains a rational $\xi$.) -/
@[kb "chenevierlannes2019" "§3.4.2, p. 65 (Weyl vectors)"]
def IsWeylVector (Q : QuadForm ℤ n) (ρ : Fin n → ℚ) : Prop :=
  ∃ ξ : Fin n → ℚ, (∀ α ∈ rootSet Q, bQ Q (cv α) ξ ≠ 0) ∧
    (2 : ℚ) • ρ = ∑ᶠ (α : Fin n → ℤ) (_ : α ∈ rootSet Q ∧ 0 < bQ Q (cv α) ξ), cv α

/-- **Proposition 3.4.2.1 (Borcherds)** (Chenevier–Lannes, p. 65; named statement): a Weyl vector of a Niemeier
lattice with roots lies in $L$ (a priori it lies in $\tfrac12 L$). -/
@[kb "chenevierlannes2019" "Prop. 3.4.2.1, p. 65"]
def WeylVectorIntegral : Prop :=
  ∀ Q : QuadForm ℤ 24, IsNiemeier Q → (rootSet Q).Nonempty → ∀ ρ : Fin 24 → ℚ, IsWeylVector Q ρ →
    ∃ r : Fin 24 → ℤ, ρ = cv r

/-- **The $d$-neighbour $\mathrm{vois}_d(L; u)$** (Chenevier–Lannes, §3.1, after Proposition 3.1.5, p. 48): for
$u \in L$ with $q(u) \equiv 0 \bmod d$ and $v \in L$ with $u \cdot v \equiv 1 \bmod d$, the lattice of $\mathbb{Q}^n$
generated by $M_d(L; u) = \{x \in L : u \cdot x \equiv 0 \bmod d\}$ and $\frac1d\,(u - q(u)\,v)$. (By Proposition 3.1.4
it is a $d$-neighbour of $L$, depending only on the line $[u] \in C_L(\mathbb{Z}/d)$; not formalized here.) -/
@[kb "chenevierlannes2019" "§3.1, p. 48 (vois_d(L; u))"]
def voisLat (Q : QuadForm ℤ n) (d : ℕ) (u v : Fin n → ℤ) : Submodule ℤ (Fin n → ℚ) :=
  Submodule.span ℤ ({x | ∃ y : Fin n → ℤ, x = cv y ∧ (d : ℤ) ∣ bZ Q u y} ∪
    {(1 / (d : ℚ)) • cv (u - Q.eval u • v)})

/-- **Theorem 3.4.2.10 (a), (c): the holy constructions** (Chenevier–Lannes, p. 69; (1.2.1), p. 5; Conway–Sloane;
named statement): let $L$ be a Niemeier lattice with roots, $h = h(L)$, and $\rho \in L$ a Weyl vector. For
$d = h$ and $d = h + 1$:
(a) $\rho$ is $d$-primitive with $q(\rho) \equiv 0 \bmod d$ (its class lies on the quadric $C_L(\mathbb{Z}/d)$): some
$v \in L$ has $\rho \cdot v \equiv 1 \bmod d$, and $d \mid q(\rho)$;
(c) for every such $v$, $\mathrm{vois}_d(L; \rho)$ (`voisLat`) has a basis $g$ in which its form is a Niemeier
lattice without roots: $\mathrm{vois}_h(L; \rho) \cong \mathrm{vois}_{h+1}(L; \rho) \cong \mathrm{Leech}$.
Part (b) (the two are exchanged by $s_\rho$) and part (d) (the counts $N_h(L, \mathrm{Leech}) = |W|/(\varphi(h)g)$,
$N_{h+1}(L, \mathrm{Leech}) = |W|/\varphi(h+1)$, (1.2.2)) are not stated: the library's neighbour counts are for
prime $d$ only. -/
@[kb "chenevierlannes2019" "Thm. 3.4.2.10 (a), (c), p. 69; (1.2.1), p. 5"]
def HolyConstructions : Prop :=
  ∀ Q : QuadForm ℤ 24, IsNiemeier Q → (rootSet Q).Nonempty → ∀ ρ : Fin 24 → ℤ, IsWeylVector Q (cv ρ) →
    ∀ d : ℕ, ((d : ℚ) = coxeterNumber Q ∨ (d : ℚ) = coxeterNumber Q + 1) →
      ((∃ v : Fin 24 → ℤ, (d : ℤ) ∣ bZ Q ρ v - 1) ∧ (d : ℤ) ∣ Q.eval ρ) ∧
      ∀ v : Fin 24 → ℤ, (d : ℤ) ∣ bZ Q ρ v - 1 →
        ∃ (g : Matrix (Fin 24) (Fin 24) ℚ) (P : QuadForm ℤ 24), g.det ≠ 0 ∧ imgLat g = voisLat Q d ρ v ∧
          (∀ x, P.evalIn ℚ x = Q.evalIn ℚ (g *ᵥ x)) ∧ IsLeechType P

end QuadFormsKB.ChenevierLannes
