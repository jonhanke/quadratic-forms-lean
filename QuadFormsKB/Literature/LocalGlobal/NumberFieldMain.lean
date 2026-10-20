/-
# Local–global statements over a number field $F$, downstream of their proofs

These statements are the inputs bundled in `NumberField.lean` and `NumberFieldInputs.lean`,
which are imported by the files that prove them. They live here, with the same names,
docstrings and `@[kb]` tags, so that each can cite its proof:

- `hilbert_reciprocity_nf`: `HN.hilbert_product_formula_nf` (`HasseNorm/Reciprocity.lean`);
- `represents_iff_everywhere_nf`: from `hasseMinkowski_nf` (`HasseMinkowskiNFMain.lean`) and
  `QuadForm.representsIn_iff_isotropicIn_orthSum` (`Witt/Represents.lean`);
- `NFInputs.isSquare_iff_everywhere_nf`: `SqLG.isSquare_iff_everywhere`;
- `NFInputs.hilbert_eq_one_of_everywhere_nf`: `HasseNorm.hilbert_eq_one_of_everywhere`;
- `NFInputs.hilbertSymbol_mul_left_finite_nf`: `HN.hilbertSymbol_mul_left_finite_nf`;
- `NFInputs.exists_prescribed_hilbert_nf`: `PresNF.exists_prescribed_hilbert` (`PrescribedNF.lean`).

So all five inputs of the Serre-route bundle `NFInputs.hmInputs` are proved, and Serre's route to Hasse–Minkowski
over $F$ is a second, unconditional proof alongside Lam's (`lamInputs`, `hasseMinkowski_nf`).

Locators are from memory and still `[unverified]`.
-/
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowskiNFMain
import QuadFormsKB.Literature.HasseNorm.Reciprocity
import QuadFormsKB.Witt.Represents
import QuadFormsKB.Literature.LocalGlobal.PrescribedNF

open NumberField

namespace QuadFormsKB

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- **Hilbert reciprocity over a number field $F$:** for $a, b \in F^\times$, the local symbol
$(a,b)_v$ is $-1$ at only finitely many places $v$, and at an even number of them
(equivalently $\prod_v (a,b)_v = 1$). Proved as `HN.hilbert_product_formula_nf`
(`HasseNorm/Reciprocity.lean`: Weil index + adelic Poisson summation), same
statement. -/
@[kb "omeara1963" "§71:18 [unverified]"]
theorem hilbert_reciprocity_nf (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    {v : NFPlace F | v.hilbert a b = -1}.Finite ∧
      Even {v : NFPlace F | v.hilbert a b = -1}.ncard :=
  HN.hilbert_product_formula_nf a b ha hb

/-- **Local–global representation over a number field $F$:** a nondegenerate form over $F$
represents $c \in F^\times$ over $F$ iff it represents $c$ over every completion $F_v$.

*Proof* (O'Meara 66:3; Serre IV §3.2, Cor. 1). Over any field $K \supseteq F$, $Q$ represents $c \ne 0$
iff $Q \perp \langle -c \rangle$ is isotropic (`QuadForm.representsIn_iff_isotropicIn_orthSum`); apply
`hasseMinkowski_nf` to the nondegenerate form $Q \perp \langle -c \rangle$. -/
@[kb "omeara1963" "§66:3 [unverified]"]
theorem represents_iff_everywhere_nf (Q : QuadForm F n) (hQ : Q.Nondegenerate) (c : F)
    (hc : c ≠ 0) :
    Q.RepresentsIn F c ↔ NFPlace.Everywhere (F := F) fun K _ _ => Q.RepresentsIn K c := by
  have hc' : ∀ i, (![-c] : Fin 1 → F) i ≠ 0 := fun i => by
    simpa [Subsingleton.elim i 0] using hc
  rw [QuadForm.representsIn_iff_isotropicIn_orthSum F hQ c,
    hasseMinkowski_nf _ (QuadForm.nondegenerate_orthSum hQ (QuadForm.nondegenerate_diag hc'))]
  refine forall_congr' fun v => ?_
  cases v with
  | infinite w => exact (QuadForm.representsIn_iff_isotropicIn_orthSum w.Completion hQ c).symm
  | finite v =>
    exact (QuadForm.representsIn_iff_isotropicIn_orthSum (v.adicCompletion F) hQ c).symm

namespace NFInputs

/-- **Input: squares are local–global over a number field $F$.** An element $a \in F$ is a square
in $F$ iff it is a square in every completion $F_v$. (For $F = \mathbb{Q}$ this is
`isSquare_iff_everywhere`, proved. For general $F$ it follows from the Chebotarev density theorem or
from class field theory.) Proved as `SqLG.isSquare_iff_everywhere` (`SquaresLocalGlobal.lean`),
same statement. -/
@[kb "omeara1963" "§65:15 [unverified]"]
theorem isSquare_iff_everywhere_nf (a : F) :
    IsSquare a ↔ NFPlace.Everywhere (F := F) fun K _ _ => IsSquare (algebraMap F K a) :=
  SqLG.isSquare_iff_everywhere a

/-- **Input: elements of $F$ with prescribed local Hilbert symbols** (the number-field analogue of
Serre III §2.2, Thm. 4). Let $a_i \in F^\times$ ($i$ in a finite set) and signs
$\varepsilon_{i,v} \in \{\pm 1\}$ at the places $v$ of $F$, with (1) only finitely many $-1$'s,
(2) an even number of $-1$'s for each $i$, and (3) at each $v$ some $x_v \in F_v^\times$ with
$(a_i, x_v)_v = \varepsilon_{i,v}$ for all $i$. Then some $x \in F^\times$ has
$(a_i, x)_v = \varepsilon_{i,v}$ for all $i, v$. Proved as `PresNF.exists_prescribed_hilbert`
(`PrescribedNF.lean`), same statement, without class field theory: the $S$-unit Lagrangian in
$\prod_{v \in S\cup\infty}F_v^\times/F_v^{\times2}$ (Hilbert reciprocity and square-class counts), finite duality, and
primes with prescribed square classes from Dedekind's density argument.

*Update (locator):* O'Meara 71:19 (printed p. 203; checked 2026-10-17) is only the case of one $a_i$ (with
Cor. 71:19a); the statement for several $a_i$ is Serre's Thm. 4, stated there over $\mathbb Q$. -/
@[kb "omeara1963" "§71:19 and 71:19a (case of one a_i; checked); serre1973 Ch. III §2.2, Thm. 4 (several a_i, over Q)"]
theorem exists_prescribed_hilbert_nf {ι : Type} [Fintype ι] (a : ι → F) (ha : ∀ i, a i ≠ 0)
    (ε : ι → NFPlace F → ℤ) (hε : ∀ i v, ε i v = 1 ∨ ε i v = -1)
    (h1 : {v : NFPlace F | ∃ i, ε i v = -1}.Finite)
    (h2 : ∀ i, Even {v : NFPlace F | ε i v = -1}.ncard)
    (h3 : ∀ v : NFPlace F, v.atPlace fun K _ _ =>
      ∃ x : K, x ≠ 0 ∧ ∀ i, hilbertSymbol K (algebraMap F K (a i)) x = ε i v) :
    ∃ x : F, x ≠ 0 ∧ ∀ i v, v.hilbert (a i) x = ε i v :=
  PresNF.exists_prescribed_hilbert a ha ε hε h1 h2 h3

/-- **Input: the Hasse norm theorem for quadratic extensions of $F$.** For $a, b \in F^\times$, if the
local Hilbert symbol $(a,b)_v = 1$ at every place $v$ of $F$, then $(a,b)_F = 1$; that is,
$z^2 = a x^2 + b y^2$ has a nonzero solution in $F$. Equivalently: if $b$ is a norm from
$F_v(\sqrt{a})$ at every $v$, it is a norm from $F(\sqrt{a})$. (For $F = \mathbb{Q}$ this is
`HM3.hilbert_rat_eq_one_of_everywhere`, proved by Legendre's descent. For general $F$ it comes from
class field theory; it is exactly the ternary case of Hasse–Minkowski.) Proved as
`HasseNorm.hilbert_eq_one_of_everywhere` (`HasseNorm/Main.lean`), same statement. -/
@[kb "omeara1963" "§65 (Hasse norm theorem) [unverified]"]
theorem hilbert_eq_one_of_everywhere_nf (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ v : NFPlace F, v.hilbert a b = 1) : hilbertSymbol F a b = 1 :=
  HasseNorm.hilbert_eq_one_of_everywhere a b ha hb h

open IsDedekindDomain in
/-- **Input: the local Hilbert symbol at a finite place is multiplicative in its first argument.**
For a nonzero prime $\mathfrak{p}$ of $\mathcal{O}_F$ and $a, b, c \in F_{\mathfrak{p}}^\times$,
$(ab, c)_{\mathfrak{p}} = (a, c)_{\mathfrak{p}} \, (b, c)_{\mathfrak{p}}$. (For $\mathbb{Q}_p$ this is
proved from the explicit formulas (`hilbertSymbol_padic_mul_left`). For a general non-archimedean
local field, and especially above $2$, it is the quadratic case of local class field theory:
$[F_{\mathfrak{p}}^\times : N(L^\times)] = 2$ for each quadratic extension $L$. O'Meara proves it
directly from the local square theorem.) Proved as `HN.hilbertSymbol_mul_left_finite_nf`
(`HasseNorm/LocalIndexTwo.lean`), same statement. -/
@[kb "omeara1963" "§63 [unverified]"]
theorem hilbertSymbol_mul_left_finite_nf (v : HeightOneSpectrum (𝓞 F))
    (a b c : v.adicCompletion F) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    hilbertSymbol (v.adicCompletion F) (a * b) c =
      hilbertSymbol (v.adicCompletion F) a c * hilbertSymbol (v.adicCompletion F) b c :=
  HN.hilbertSymbol_mul_left_finite_nf v a b c ha hb hc

/-- **The inputs hold** (all five proved above; the last, `exists_prescribed_hilbert_nf`): `HMInputs F`
assembled from them. So Serre's route (`HN.hmInputs_of_prescribed`, `HasseMinkowskiNF.lean`) is unconditional too. -/
@[kb "omeara1963" "§§63, 65, 71 [unverified]"]
theorem hmInputs : HMInputs F :=
  ⟨hilbert_reciprocity_nf, isSquare_iff_everywhere_nf,
    fun a ha ε hε h1 h2 h3 => exists_prescribed_hilbert_nf a ha ε hε h1 h2 h3,
    hilbert_eq_one_of_everywhere_nf, hilbertSymbol_mul_left_finite_nf⟩

end NFInputs

/-- **Hasse–Minkowski over a number field $F$, Serre's route:** a nondegenerate quadratic form over $F$ is
isotropic over $F$ iff it is isotropic over every completion $F_v$. This is `hasseMinkowski_nf_of_inputs` (Serre
IV §3.2 over $F$) applied to `NFInputs.hmInputs`, now unconditional: a second proof of `hasseMinkowski_nf`
(Lam's route), independent of Lam's passage to quadratic extensions. -/
@[kb "serre1973" "Ch. IV §3.2, Thm. 8 (over a number field; Serre's route)"]
theorem hasseMinkowski_nf_serre (Q : QuadForm F n) (hQ : Q.Nondegenerate) :
    Q.IsotropicIn F ↔ NFPlace.Everywhere (F := F) fun K _ _ => Q.IsotropicIn K :=
  hasseMinkowski_nf_of_inputs NFInputs.hmInputs Q hQ

end QuadFormsKB
