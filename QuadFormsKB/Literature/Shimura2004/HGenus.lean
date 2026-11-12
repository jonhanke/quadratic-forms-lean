/-
# Shimura 2004, §§11.4–11.6 and §13.11–13.13: the H-genus, Theorem 11.6 and Theorem 13.12

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), §11.4–Theorem 11.6 (printed
pp. 103–105), §13.11–(13.18) (pp. 133–134). Page numbers are printed pages.

**Setting and dictionary.** $F$ is a number field with maximal order $\mathfrak g = \mathcal O_F$ and
$V = F^n$ with the form `Q : QuadForm F n`, $\varphi[x] = Q(x)$ (the library's coordinate lattices `Lat F n`; every
$n$-dimensional quadratic space over $F$ is isometric to one of these). Shimura lets matrices act on the right
($x\alpha$, $L\alpha$); here they act on the left ($\gamma x$ = `γ.val *ᵥ x`, $\gamma L$ = `Lat.image γ L`), so
the book's $L\alpha^{-1}$ is $\alpha^{-1}L$ here, and so on.
* $G = SO^\varphi(V)$ is `Tamagawa.soSub Q F` (inside `orthGroup Q F`); $\Gamma(\Lambda) = \{\gamma\in G \mid
  \Lambda\gamma = \Lambda\}$ (11.3a) is `gammaLat Q Λ`.
* For $h \in V$ with $\varphi[h] \ne 0$ and $W = (Fh)^\perp$, $H = SO^\varphi(W)$, viewed (as in the book) as the
  subgroup of $G$ acting trivially on $Fh$: `hRat Q h` $= \{\gamma \in G \mid \gamma h = h\}$.
* Adelizations: the library's finite adelic orthogonal group $O^\varphi(V)_{\mathbf h}$ = `Lattices.OAf Q`
  (restricted product over the finite primes) acting on lattices (`Lattices.latAction`); $G_{\mathbf h}$ =
  `Tamagawa.soAf Q`, and $H_{\mathbf h}$ = `hAf Q h` (the elements of $G_{\mathbf h}$ fixing $h$ at every prime).
  Shimura's $G_{\mathbb A}$, $H_{\mathbb A}$ include the archimedean factors, but these act trivially on lattices
  and lie in $C$, so $H\backslash H_{\mathbb A}/(H_{\mathbb A}\cap C) = H\backslash H_{\mathbf h}/(H_{\mathbf h}\cap
  C_{\mathbf h})$ and the $H$-genus and $H$-class (§9.3) only see the finite part.
* The $H$-genus of $\Lambda$ (§9.3, used in §11.4) is the orbit $\Lambda H_{\mathbb A}$ (`hGenus Q h Λ`), the
  $H$-class of $\Lambda$ is the orbit under $H$ (`HClassRel`); the $G$-genus and $G$-class likewise (`soGenus`,
  `SOClassRel`).
* $C = \{x \in G_{\mathbb A} \mid Lx = L\}$ (11.4) is `soAf Q ⊓ locStab Q L` (finite part).
* $\Lambda[q,\mathfrak b]$ (11.3b) and $\varphi(x,\Lambda)$ are `solSet`/`phiIdeal` of `Diophantine.lean`, for the
  Mathlib form `Q.toQuadraticForm` with $\mathfrak g = \mathcal O_F$; $\Lambda[q,\mathfrak b]/\Gamma(\Lambda)$ is
  `solOrbits Q Λ q b`.
* (9.2): if $n$ is odd, the discriminant of $\varphi$ is represented at every finite prime $v$ by a unit of
  $\mathfrak g_v$ (`Cond92`; $\det$ of the Gram matrix $\tfrac12(C + {}^tC)$ of $\varphi$, the sign
  $(-1)^{n(n-1)/2}$ of the discriminant of §1.5 being a unit).

**States** (named propositions, not proved here: the proofs need Theorem 10.5, the local transitivity theorem, which
is itself only stated in `Diophantine.lean`)
* `Theorem11_6_i`: the fundamental theorem (11.7): for a minimal set $\{L_i\}$ of $G$-class representatives
  covering the $H$-genus of the $\mathfrak g$-maximal lattice $L$,
  $\#[H\backslash H_{\mathbb A}/(H_{\mathbb A}\cap C)] = \sum_i\#(L_i[q,\mathfrak b]/\Gamma(L_i))$ and this is the
  number of $H$-classes in the $H$-genus of $L$;
* `Theorem11_6_v`: for $\Lambda$ in the $G$-genus of $L$, $\Lambda[q,\mathfrak b] \ne \emptyset$ iff $\Lambda$ is
  $G$-equivalent to some $L_i$;
* `Formula13_18`: (13.18), the definite case of Theorem 13.12 (13.17b):
  $\sum_i[\Gamma(L_i):1]^{-1}\#L_i[q,\mathfrak b] = m(H, H_{\mathbb A}\cap C)$, the right side the library's
  double coset mass `Tamagawa.dcMass` (Shimura's (13.12c)).

* `Theorem12_14_iv`: Theorem 12.14 (iv) for the sum of $n = 5, 7, 9$ squares,
  $\#\{L[q,\mathbb Z]/\Gamma(L)\} = \#(H\backslash H_{\mathbb A}/E)$.

**Proves** (standard axioms only)
* unconditionally: the definitions are well formed (`hRat_le_soSub`, `hAf_le_soAf`, `gammaLat_le_soSub`,
  `diagF_mem_hAf`: the rational points of $H$ lie in $H_{\mathbf h}$, `mem_hGenus_self`, `hGenus_subset_soGenus`:
  the $H$-genus lies in the $G$-genus); the sum of squares satisfies (9.2) and is nondegenerate (`sosQ_cond92`,
  `sosQ_nondegenerate`);
* conditional on the named inputs `FundamentalTheorem11_6` (Theorem 11.6 (i)) and `SumSquaresOneClass`
  ([S02a, Lemma 1.6]): `theorem_12_14_iv`, Theorem 12.14 (iv), by Shimura's argument ($\{L_i\} = \{L\}$ in (11.7)).
-/
import QuadFormsKB.Literature.Shimura2004.Diophantine
import QuadFormsKB.Tamagawa.MassFormula
import QuadFormsKB.Tamagawa.OrbitMass
import Mathlib.GroupTheory.DoubleCoset
import QuadFormsKB.Citation

open NumberField IsDedekindDomain Matrix
open scoped RestrictedProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-! ### The groups $G$, $H$, $\Gamma(\Lambda)$ and their adelizations -/

/-- The stabilizer $\{g \in O^\varphi(V)(R) \mid g x = x\}$ of a vector $x \in R^n$, for an $F$-algebra $R$. -/
def fixSub (R : Type*) [CommRing R] [Algebra F R] (x : Fin n → R) : Subgroup (orthGroup Q R) where
  carrier := {g | (g : GL (Fin n) R).val *ᵥ x = x}
  mul_mem' {a b} ha hb := by
    change ((a : GL (Fin n) R) * (b : GL (Fin n) R)).val *ᵥ x = x
    rw [Units.val_mul, ← mulVec_mulVec, show (b : GL (Fin n) R).val *ᵥ x = x from hb,
      show (a : GL (Fin n) R).val *ᵥ x = x from ha]
  one_mem' := by
    change (1 : GL (Fin n) R).val *ᵥ x = x
    simp
  inv_mem' {a} ha := by
    change ((a : GL (Fin n) R)⁻¹).val *ᵥ x = x
    conv_lhs => rw [← show (a : GL (Fin n) R).val *ᵥ x = x from ha]
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

/-- **$H = SO^\varphi(W)$, $W = (Fh)^\perp$, as a subgroup of $G = SO^\varphi(V)$** (Shimura 2004, Theorem 11.6,
p. 104: "we consider $H'$ a subgroup of $G'$ by defining the action of $H'$ on $Fh$ to be trivial"): the
$\gamma \in SO^\varphi(V)$ with $\gamma h = h$ (such $\gamma$ preserve $W$, and every element of $SO^\varphi(W)$
extends uniquely in this way). -/
@[kb "shimura2004" "Thm. 11.6, p. 104 (H = SO^φ(W) ⊆ SO^φ(V), acting trivially on Fh)"]
def hRat (h : Fin n → F) : Subgroup (orthGroup Q F) := soSub Q F ⊓ fixSub Q F h

theorem hRat_le_soSub (h : Fin n → F) : hRat Q h ≤ soSub Q F := inf_le_left

/-- **$H_{\mathbf h}$**: the elements of $G_{\mathbf h} = SO^\varphi(V)_{\mathbf h}$ (`soAf Q`) whose component at
every finite prime $v$ fixes $h \in V \subseteq V_v$ (Shimura 2004, §11.4, p. 103 and Theorem 11.6, p. 104: the
adelization of $H = SO^\varphi(W)$, viewed inside $G_{\mathbb A}$; finite part). -/
@[kb "shimura2004" "Thm. 11.6, p. 104 (H_𝔸 ⊆ G_𝔸, finite part)"]
def hAf (h : Fin n → F) : Subgroup (OAf Q) where
  carrier := {g | g ∈ soAf Q ∧ ∀ v : HeightOneSpectrum (𝓞 F),
    g v ∈ fixSub Q (v.adicCompletion F) (fun i => algebraMap F (v.adicCompletion F) (h i))}
  mul_mem' {a b} ha hb := ⟨(soAf Q).mul_mem ha.1 hb.1, fun v => by
    have := (fixSub Q (v.adicCompletion F) _).mul_mem (ha.2 v) (hb.2 v)
    exact this⟩
  one_mem' := ⟨(soAf Q).one_mem, fun v => (fixSub Q (v.adicCompletion F) _).one_mem⟩
  inv_mem' {a} ha := ⟨(soAf Q).inv_mem ha.1, fun v => by
    have := (fixSub Q (v.adicCompletion F) _).inv_mem (ha.2 v)
    exact this⟩

theorem hAf_le_soAf (h : Fin n → F) : hAf Q h ≤ soAf Q := fun _ hg => hg.1

/-- **$\Gamma(\Lambda) = \{\gamma \in SO^\varphi(V) \mid \Lambda\gamma = \Lambda\}$** (Shimura 2004, (11.3a),
p. 103), for a lattice $\Lambda$ of the number field $F$ (`autLat` is the full stabilizer in $O^\varphi(V)$). -/
@[kb "shimura2004" "(11.3a), p. 103 (Γ(Λ) = {γ ∈ SO^φ(V) | Λγ = Λ})"]
def gammaLat (Λ : Lat F n) : Subgroup (orthGroup Q F) := soSub Q F ⊓ autLat Q Λ.1

theorem gammaLat_le_soSub (Λ : Lat F n) : gammaLat Q Λ ≤ soSub Q F := inf_le_left

/-- **$C = \{x \in G_{\mathbb A} \mid Lx = L\}$** (Shimura 2004, (11.4), p. 103; finite part): the stabilizer of
$L$ in $SO^\varphi(V)_{\mathbf h}$. -/
@[kb "shimura2004" "(11.4), p. 103 (C = {x ∈ SO^φ(V)_𝔸 | Lx = L})"]
def stabC (L : Lat F n) : Subgroup (OAf Q) := soAf Q ⊓ locStab Q L

/-! ### Genera and classes with respect to $G$ and $H$ (§9.3, §11.4) -/

/-- **The $G$-genus of $\Lambda$** for $G = SO^\varphi(V)$ (Shimura 2004, §9.3 and §11.4, p. 103): the orbit of
$\Lambda$ under $G_{\mathbb A}$ (finite part `soAf Q`, acting by `latAction`). -/
@[kb "shimura2004" "§9.3; §11.4, p. 103 (the SO^φ(V)-genus of Λ)"]
def soGenus (Λ : Lat F n) : Set (Lat F n) :=
  letI := latAction Q
  {M | ∃ g ∈ soAf Q, g • Λ = M}

/-- **The $H$-genus of $\Lambda$** (Shimura 2004, §9.3 and §11.4, p. 103): the orbit of $\Lambda$ under
$H_{\mathbb A}$, $H = SO^\varphi(W)$ (finite part `hAf Q h`). -/
@[kb "shimura2004" "§9.3; §11.4, p. 103 (the H-genus of Λ)"]
def hGenus (h : Fin n → F) (Λ : Lat F n) : Set (Lat F n) :=
  letI := latAction Q
  {M | ∃ g ∈ hAf Q h, g • Λ = M}

/-- **Same $G$-class** (Shimura 2004, §9.3; §11.4): $M = \gamma\Lambda$ for some $\gamma \in SO^\varphi(V)$. -/
@[kb "shimura2004" "§9.3; §11.4, p. 103 (the SO^φ(V)-class of Λ)"]
def SOClassRel (Λ M : Lat F n) : Prop := ∃ γ ∈ soSub Q F, Lat.image (γ : GL (Fin n) F) Λ = M

/-- **Same $H$-class** (Shimura 2004, §9.3; §11.4): $M = \gamma\Lambda$ for some $\gamma \in H$. -/
@[kb "shimura2004" "§9.3; §11.4, p. 103 (the H-class of Λ)"]
def HClassRel (h : Fin n → F) (Λ M : Lat F n) : Prop := ∃ γ ∈ hRat Q h, Lat.image (γ : GL (Fin n) F) Λ = M

/-- **The set of $H$-classes in the $H$-genus of $L$** (Shimura 2004, Theorem 11.6 (i), p. 104): the quotient of
`hGenus Q h L` by `HClassRel` (a `Quot`, so no equivalence-relation proof is needed to state the count). -/
def hClassesInHGenus (h : Fin n → F) (L : Lat F n) : Type :=
  Quot fun M M' : hGenus Q h L => HClassRel Q h M.1 M'.1

/-! ### Solutions and orbits -/

/-- **$\Lambda[q, \mathfrak b]$** (Shimura 2004, (11.3b), p. 103) for a lattice of the number field $F$: the
$x \in V$ with $\varphi[x] = q$ and $\varphi(x, \Lambda) = \mathfrak b$ (`solSet` for `Q.toQuadraticForm`,
$\mathfrak g = \mathcal O_F$). -/
@[kb "shimura2004" "(11.3b), p. 103 (Λ[q, 𝔟], number field case)"]
def solSetLat (Λ : Lat F n) (q : F) (b : Submodule (𝓞 F) F) : Set (Fin n → F) :=
  letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  solSet Q.toQuadraticForm Λ.1 q b

/-- **$\Lambda[q,\mathfrak b]/\Gamma(\Lambda)$** (Shimura 2004, §11.4, p. 103: "$\Gamma(\Lambda)$ acts on the right
of $\Lambda[q,\mathfrak b]$"): the orbits of $\Gamma(\Lambda)$ on $\Lambda[q, \mathfrak b]$. -/
@[kb "shimura2004" "§11.4, p. 103 (Λ[q, 𝔟]/Γ(Λ))"]
def solOrbits (Λ : Lat F n) (q : F) (b : Submodule (𝓞 F) F) : Type :=
  Quot fun x y : solSetLat Q Λ q b => ∃ γ ∈ gammaLat Q Λ, (γ : GL (Fin n) F).val *ᵥ x.1 = y.1

/-! ### Hypotheses of Theorem 11.6 -/

/-- **Condition (9.2)** (Shimura 2004, §9.2, p. 78): if $n$ is odd, then for every finite prime $v$ the
discriminant of $\varphi_v$ is represented by an element of $\mathfrak g_v^\times$: the determinant of the Gram
matrix $\tfrac12(C + {}^tC)$ of $\varphi$ (`Q.hessian` $= C + {}^tC$) is a unit of $\mathfrak g_v$ times a nonzero
square of $F_v$. -/
@[kb "shimura2004" "(9.2), p. 78 (n odd ⇒ the discriminant is represented by a unit of 𝔤_v for every v)"]
def Cond92 : Prop :=
  Odd n → ∀ v : HeightOneSpectrum (𝓞 F), ∃ (u : (v.adicCompletionIntegers F)ˣ) (c : v.adicCompletion F), c ≠ 0 ∧
    algebraMap F (v.adicCompletion F) (((1 / 2 : F) • Q.hessian).det) = (u : v.adicCompletion F) * c ^ 2

/-- **$\mathfrak g$-maximal lattice** (Shimura 2004, §6.1 and §11.4, p. 103): $\varphi[x] \in \mathfrak g$ on $L$,
and $L$ is maximal for this property (O'Meara's $\mathfrak g$-maximal lattice, `OMeara.IsMaximal` with norm
ideal $\mathfrak g$, for `Q.toQuadraticForm`). -/
@[kb "shimura2004" "§6.1, p. 47; §11.4, p. 103 (𝔤-maximal lattice)"]
def IsGMaximal (L : Lat F n) : Prop :=
  letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  OMeara.IsMaximal Q.toQuadraticForm (1 : Submodule (𝓞 F) F) L.1

/-- **A minimal set of $G$-class representatives covering the $H$-genus** (Shimura 2004, Theorem 11.6 (i), p. 104):
a finite family $(L_i)_{i \in I}$ in the $H$-genus of $L$ such that every member of the $H$-genus is $G$-equivalent
to some $L_i$, and no two $L_i$ are $G$-equivalent (minimality). -/
structure IsHGenusCover (h : Fin n → F) (L : Lat F n) {I : Type} (Ls : I → Lat F n) : Prop where
  mem : ∀ i, Ls i ∈ hGenus Q h L
  cover : ∀ M ∈ hGenus Q h L, ∃ i, SOClassRel Q (Ls i) M
  minimal : ∀ i j, SOClassRel Q (Ls i) (Ls j) → i = j

/-- The double coset space $H\backslash H_{\mathbb A}/(H_{\mathbb A}\cap C)$ (finite part), as the double cosets of
the subgroups $H$ (diagonally embedded) and $H_{\mathbf h} \cap C$ of the group $H_{\mathbf h}$. -/
def hDoubleCosets (h : Fin n → F) (L : Lat F n) : Type :=
  DoubleCoset.Quotient ((((hRat Q h).map (diagF Q)).subgroupOf (hAf Q h) : Subgroup (hAf Q h)) : Set (hAf Q h))
    (((stabC Q L).subgroupOf (hAf Q h) : Subgroup (hAf Q h)) : Set (hAf Q h))

/-! ### Theorem 11.6 -/

/-- **Theorem 11.6 (i) and (11.7)** (Shimura 2004, p. 104), the fundamental theorem: let $F$ be a number field,
$(V,\varphi)$ nondegenerate with $\dim V > 2$ satisfying (9.2), $L$ a $\mathfrak g$-maximal lattice, $h \in V$ with
$q = \varphi[h] \ne 0$, $\mathfrak b = \varphi(h, L)$, $W = (Fh)^\perp$, $G = SO^\varphi(V)$, $H = SO^\varphi(W)$, and
$\{L_i\}_{i\in I}$ a minimal subset of the $H$-genus of $L$ whose $G$-classes cover it. Then the $L_i[q,\mathfrak b]/
\Gamma(L_i)$, $i \in I$, are in bijection with the $H$-classes in the $H$-genus of $L$ (Shimura's map: $k = h\alpha
\mapsto$ the $H$-class of $L_i\alpha^{-1}$), all these sets are finite, and
$$\#[H\backslash H_{\mathbb A}/(H_{\mathbb A}\cap C)] = \sum_{i\in I}\#(L_i[q,\mathfrak b]/\Gamma(L_i)).\qquad(11.7)$$
*Stated, not proved* (the proof uses Theorem 10.5 at every prime). -/
@[kb "shimura2004" "Thm. 11.6 (i) and (11.7), p. 104 (#H\\H_𝔸/(H_𝔸 ∩ C) = Σ #(L_i[q, 𝔟]/Γ(L_i)))"]
def Theorem11_6_i : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (Q : QuadForm F n), Q.Nondegenerate →
    2 < n → Cond92 Q → ∀ L : Lat F n, IsGMaximal Q L → ∀ h : Fin n → F, Q.eval h ≠ 0 →
    letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
    let b := phiIdeal Q.toQuadraticForm h L.1
    ∀ (I : Type) (Ls : I → Lat F n), IsHGenusCover Q h L Ls →
      Finite I ∧ (∀ i, Finite (solOrbits Q (Ls i) (Q.eval h) b)) ∧
      Nonempty ((Σ i, solOrbits Q (Ls i) (Q.eval h) b) ≃ hClassesInHGenus Q h L) ∧
      Nat.card (hDoubleCosets Q h L) = ∑ᶠ i, Nat.card (solOrbits Q (Ls i) (Q.eval h) b)

/-- **Theorem 11.6 (v)** (Shimura 2004, p. 104): with the notation of Theorem 11.6 (i), a lattice $\Lambda$ in the
$G$-genus of $L$ has $\Lambda[q, \mathfrak b] \ne \emptyset$ if and only if $\Lambda$ is in the $G$-class of some
$L_i$; so $\{L_i\}$ may be replaced by a full set of representatives of the $G$-classes in the $G$-genus of $L$
(adding zeros to (11.7)). *Stated, not proved.* -/
@[kb "shimura2004" "Thm. 11.6 (v), p. 104 (Λ[q, 𝔟] ≠ ∅ iff Λ is G-equivalent to some L_i)"]
def Theorem11_6_v : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (Q : QuadForm F n), Q.Nondegenerate →
    2 < n → Cond92 Q → ∀ L : Lat F n, IsGMaximal Q L → ∀ h : Fin n → F, Q.eval h ≠ 0 →
    letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
    let b := phiIdeal Q.toQuadraticForm h L.1
    ∀ (I : Type) (Ls : I → Lat F n), IsHGenusCover Q h L Ls →
      ∀ Λ ∈ soGenus Q L, (solSetLat Q Λ (Q.eval h) b).Nonempty ↔ ∃ i, SOClassRel Q (Ls i) Λ

/-! ### Theorem 13.12 in the definite case: (13.18) -/

/-- **(13.18)**, the totally definite case of **Theorem 13.12 (13.17b)** (Shimura 2004, pp. 134–135): with the
notation and assumptions of Theorem 11.6, and $O^\varphi(V)_{\mathbf a}$ compact ($F$ totally real and $\varphi$
totally positive definite),
$$\sum_{i\in I}[\Gamma(L_i):1]^{-1}\,\#L_i[q,\mathfrak b] = m(H, H_{\mathbb A}\cap C),$$
where $m(H, U) = \sum_{a\in H\backslash H_{\mathbb A}/U}[H\cap aUa^{-1}:1]^{-1}$ (13.12c) is the library's double
coset mass `Tamagawa.dcMass` inside $H_{\mathbf h}$. The left side is Siegel's weighted average restricted to the
solutions with $\varphi(x, L_i) = \mathfrak b$, over the $SO^\varphi(W)$-genus only; the right side is the mass of
the $(n-1)$-dimensional group $H$ (§13.13). *Stated, not proved* (it follows from Theorem 11.6 (ii)). -/
@[kb "shimura2004" "(13.18), p. 134; Thm. 13.12 (13.17b), p. 134 (Σ [Γ(L_i):1]⁻¹ #L_i[q, 𝔟] = m(H, H_𝔸 ∩ C))"]
def Formula13_18 : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (Q : QuadForm F n), Q.Nondegenerate →
    IsTotallyPosDef Q →
    2 < n → Cond92 Q → ∀ L : Lat F n, IsGMaximal Q L → ∀ h : Fin n → F, Q.eval h ≠ 0 →
    letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
    let b := phiIdeal Q.toQuadraticForm h L.1
    ∀ (I : Type) (Ls : I → Lat F n), IsHGenusCover Q h L Ls →
      ∑ᶠ i, ((solSetLat Q (Ls i) (Q.eval h) b).ncard : ℝ) / Nat.card (gammaLat Q (Ls i)) =
        dcMass (((hRat Q h).map (diagF Q)).subgroupOf (hAf Q h)) ((stabC Q L).subgroupOf (hAf Q h))

/-! ### Basic facts -/

/-- The rational points of $H$ lie in $H_{\mathbf h}$. -/
theorem diagF_mem_hAf (h : Fin n → F) {γ : orthGroup Q F} (hγ : γ ∈ hRat Q h) : diagF Q γ ∈ hAf Q h := by
  refine ⟨fun v => ?_, fun v => ?_⟩
  · change ((orthMap Q (v.adicCompletion F) γ : orthGroup Q (v.adicCompletion F)) : GL (Fin n) (v.adicCompletion F)).val.det = 1
    rw [orthMap_val, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      show (γ : GL (Fin n) F).val.det = 1 from hγ.1, map_one]
  · change ((orthMap Q (v.adicCompletion F) γ : orthGroup Q (v.adicCompletion F)) : GL (Fin n) (v.adicCompletion F)).val *ᵥ _ = _
    rw [orthMap_val]
    funext i
    exact (RingHom.map_mulVec _ _ _ i).symm.trans (by rw [show (γ : GL (Fin n) F).val *ᵥ h = h from hγ.2])

theorem mem_hGenus_self (h : Fin n → F) (Λ : Lat F n) : Λ ∈ hGenus Q h Λ :=
  ⟨1, (hAf Q h).one_mem, (latAction Q).one_smul Λ⟩

theorem hGenus_subset_soGenus (h : Fin n → F) (Λ : Lat F n) : hGenus Q h Λ ⊆ soGenus Q Λ :=
  fun _ ⟨g, hg, hgΛ⟩ => ⟨g, hg.1, hgΛ⟩

/-! ### Theorem 12.14 (iv): sums of five, seven and nine squares -/

/-- The sum of $n$ squares $\varphi[x] = x\,{}^tx$ on $V = \mathbb Q^n$, as a coordinate form. -/
abbrev sosQ (n : ℕ) : QuadForm ℚ n := QuadForm.diag fun _ => 1

/-- **Cited input: the genus of $\mathbb Z$-maximal lattices for the sum of $n \le 9$ squares is one
$SO^\varphi$-class** (Shimura 2004, §12.12, p. 122: "the genus of $\mathbb Z$-maximal lattices in $V$ consists of a
single $O^\varphi$-class if $n \le 9$; for the proof, see [S02a, Lemma 1.6]", and, since $L$ has an element $k$ with
$\varphi[k] = 1$, "from Lemma 9.23 (i) and (iii) we see that the genus consists of a single $SO^\varphi$-class"), for
$n = 5, 7, 9$: every lattice in the $SO^\varphi$-genus of a $\mathbb Z$-maximal $L$ is $SO^\varphi(V)$-equivalent
to $L$. Not proved here. -/
@[kb "shimura2004" "§12.12, p. 122 (one SO^φ-class in the genus of ℤ-maximal lattices, n ≤ 9; [S02a, Lemma 1.6])"]
structure SumSquaresOneClass : Prop where
  one_class : ∀ n ∈ ({5, 7, 9} : Finset ℕ), ∀ L : Lat ℚ n, IsGMaximal (sosQ n) L →
    ∀ M ∈ soGenus (sosQ n) L, SOClassRel (sosQ n) L M

/-- **Cited input: Theorem 11.6 (i)** (the fundamental theorem, `Theorem11_6_i`), as a named structure so that its use
as a hypothesis is explicit. Stated, not proved here. -/
@[kb "shimura2004" "Thm. 11.6 (i) and (11.7), p. 104 (as an input)"]
structure FundamentalTheorem11_6 : Prop where
  holds : Theorem11_6_i

/-- **Theorem 12.14 (iv)** (Shimura 2004, p. 123), first assertion: let $n \in \{5, 7, 9\}$, $\varphi$ the sum of
$n$ squares on $V = \mathbb Q^n$, $L$ a $\mathbb Z$-maximal lattice, $h \in L[q, \mathbb Z]$ with
$q = \varphi[h] > 0$, $W = (\mathbb Q h)^\perp$, $H = SO^\varphi(W)$ and $E = \{\xi \in H_{\mathbb A} \mid
L\xi = L\}$. Then $\#\{L[q, \mathbb Z]/\Gamma(L)\} = \#(H\backslash H_{\mathbb A}/E)$ (both finite). -/
@[kb "shimura2004" "Thm. 12.14 (iv), p. 123 (#(L[q, ℤ]/Γ(L)) = #(H\\H_𝔸/E), sums of 5, 7, 9 squares)"]
def Theorem12_14_iv : Prop :=
  ∀ n ∈ ({5, 7, 9} : Finset ℕ), ∀ L : Lat ℚ n, IsGMaximal (sosQ n) L → ∀ h : Fin n → ℚ, 0 < (sosQ n).eval h →
    h ∈ solSetLat (sosQ n) L ((sosQ n).eval h) 1 →
    Finite (solOrbits (sosQ n) L ((sosQ n).eval h) 1) ∧
      Nat.card (solOrbits (sosQ n) L ((sosQ n).eval h) 1) = Nat.card (hDoubleCosets (sosQ n) h L)

theorem sosQ_half_hessian (n : ℕ) : ((1 / 2 : ℚ) • (sosQ n).hessian) = 1 := by
  ext i j
  simp only [QuadForm.hessian, QuadForm.diag, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
    Matrix.diagonal_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij; norm_num
  · simp [hij, Ne.symm hij]

theorem sosQ_nondegenerate (n : ℕ) : (sosQ n).Nondegenerate := by
  have h : (sosQ n).hessian = (2 : ℚ) • ((1 / 2 : ℚ) • (sosQ n).hessian) := by
    rw [smul_smul]; norm_num
  rw [QuadForm.Nondegenerate, h, sosQ_half_hessian, Matrix.det_smul, Matrix.det_one, mul_one]
  exact pow_ne_zero _ two_ne_zero

theorem sosQ_cond92 (n : ℕ) : Cond92 (sosQ n) := fun _ v =>
  ⟨1, 1, one_ne_zero, by rw [sosQ_half_hessian, Matrix.det_one, map_one]; simp⟩

/-- **Theorem 12.14 (iv)**, first assertion (Shimura 2004, p. 123), *conditional on two named inputs*: the
fundamental Theorem 11.6 (i) (`FundamentalTheorem11_6`) and the one-class property of the genus of
$\mathbb Z$-maximal lattices for the sum of $n \le 9$ squares (`SumSquaresOneClass`, [S02a, Lemma 1.6]). Shimura's
proof: the genus is one class, so $\{L_i\} = \{L\}$ in (11.7). -/
@[kb "shimura2004" "Thm. 12.14 (iv), p. 123 (from Theorem 11.6 (i) and one class in the genus)"]
theorem theorem_12_14_iv (hF : FundamentalTheorem11_6) (h1 : SumSquaresOneClass) : Theorem12_14_iv := by
  intro n hn L hL h _ hh
  have hb : (letI : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero
      phiIdeal (sosQ n).toQuadraticForm h L.1) = 1 := hh.2
  have hcov : IsHGenusCover (sosQ n) h L (fun _ : Unit => L) :=
    { mem := fun _ => mem_hGenus_self _ h L
      cover := fun M hM => ⟨(), h1.one_class n hn L hL M (hGenus_subset_soGenus _ h L hM)⟩
      minimal := fun _ _ _ => rfl }
  have hq : (sosQ n).eval h ≠ 0 := by
    have := ‹0 < (sosQ n).eval h›
    exact this.ne'
  obtain ⟨-, hfin, -, hcard⟩ :=
    hF.holds ℚ n (sosQ n) (sosQ_nondegenerate n) (by simp at hn; omega) (sosQ_cond92 n) L hL h hq Unit _ hcov
  simp only [hb] at hfin hcard
  refine ⟨hfin (), ?_⟩
  rw [hcard, finsum_unique]

end QuadFormsKB.Shimura2004
