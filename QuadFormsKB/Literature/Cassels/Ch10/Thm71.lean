/-
# Cassels, Chapter 10, Theorem 7.1: strong approximation for the spin group — a named statement

**Setting** (Cassels, *Rational Quadratic Forms*, Ch. 10, §§4–7, pp. 182–187). $V$ is a finite-dimensional vector
space over $\mathbb Q$ with a quadratic form $Q$ (Cassels' $\phi$); for a prime $p$, $V_p = \mathbb Q_p \otimes_{\mathbb Q} V$ with the
base-changed form `Q.baseChange ℚ_[p]` (Mathlib `QuadraticForm.baseChange`). The Clifford algebras are Mathlib's
`CliffordAlgebra Q` and `CliffordAlgebra (Q.baseChange ℚ_[p])`, the spin groups Mathlib's `spinGroup` (Cassels'
$\operatorname{Spin}(V)$ for $V \ne 0$: `Cassels.mem_spinGroup_iff`), and the natural embedding $\operatorname{Spin}(V) \to \operatorname{Spin}(V_p)$ of §6 is `spinBaseChange ℚ_[p] Q`
(`Ch10/BaseChange.lean`, induced by Mathlib's `CliffordAlgebra.ofBaseChangeAux`, $\iota(v) \mapsto \iota(1 \otimes v)$). A $\mathbb Z$-lattice $\Lambda$ (`Λ`) is a finitely
generated $\mathbb Z$-submodule of $V$ spanning $V$ over $\mathbb Q$; its localization $\Lambda_p$ (`baseChangeLat ℚ_[p] ℤ_[p] Λ`) is
the $\mathbb Z_p$-span of $1 \otimes \Lambda$ in $V_p$, and $\operatorname{Spin}(\Lambda_p) = C(\Lambda_p) \cap \operatorname{Spin}(V_p)$ is
`Cassels.intSpin` (`Ch10/IntegralClifford.lean`, (4.9)). $C(V_p)$ carries its topology as a finite-dimensional
$\mathbb Q_p$-vector space (Mathlib's `moduleTopology ℚ_[p]`), and $\operatorname{Spin}(V_p)$ the subspace topology: a subset
$\mathcal U_p \subseteq \operatorname{Spin}(V_p)$ is open when it is $O \cap \operatorname{Spin}(V_p)$ for an open $O \subseteq C(V_p)$.

**Theorem 7.1** (p. 186). Let $n \ge 3$ and let $V$ be regular and indefinite (isotropic over $\mathbb R = \mathbb Q_\infty$).
Let $\Lambda$ be a $\mathbb Z$-lattice in $V$, and for every prime $p$ let $\mathcal U_p$ be a non-empty open subset of
$\operatorname{Spin}(V_p)$, with $\mathcal U_p = \operatorname{Spin}(\Lambda_p)$ for almost all $p$ (7.3). Then there is
$u \in \operatorname{Spin}(V)$ with $u \in \mathcal U_p$ for all $p \ne \infty$ (7.4).

**Status: named statement** (`SpinStrongApproximation`, an input, not proved here). The library proves Cassels'
*Corollary* to Theorem 7.1 (strong approximation for $\Theta(V) = O'(V)$, the only form Cassels uses) unconditionally, over
every number field: `Lattices.strongApproximationSpin` (`StrongApproximationSpin`), with `Lattices.exists_strong_approx` and
`Lattices.exists_very_strong_approx`. Theorem 7.1 itself is not a formal consequence of the Corollary: a lift of
$\sigma \in \Theta$ to $\operatorname{Spin}$ is fixed only up to the centre $\{\pm 1\}$, and the sign cannot be chosen prime by prime
(it would follow where $\operatorname{Spin}(V_p)$ is perfect, i.e. $V_p$ isotropic, always for $n \ge 5$, but not at the finitely many
primes with $V_p$ anisotropic when $n = 3, 4$). A proof would follow Cassels' §7 (Lemma 7.1, i.e. Chapter 9, Theorem 1.5, for the
quaternary norm form when $n = 3$; products of symmetries and Lemma 7.2 for $n \ge 4$) or Kneser's general theorem.
-/
import QuadFormsKB.Literature.Cassels.Ch10.BaseChange

open CliffordAlgebra TensorProduct

namespace QuadFormsKB.Cassels

/-- **Cassels, Ch. 10, Theorem 7.1 (Strong Approximation Theorem for the Spin Group)** (p. 186), a named statement (not
proved; see the module docstring). Field `approx`, arguments in order: the space `V` (a finite-dimensional
$\mathbb Q$-vector space) and the form `Q`; `hn`: $\dim V \ge 3$; `hQ`: $Q$ regular; `hind`: $V$ indefinite, i.e. isotropic over
$\mathbb R$ (a nonzero $x \in \mathbb R \otimes V$ with $Q_{\mathbb R}(x) = 0$); `Λ` with `hfg`, `hspan`: a $\mathbb Z$-lattice in $V$ (finitely
generated, spanning $V$ over $\mathbb Q$); `U`: for every prime $p$ a subset $\mathcal U_p$ of $\operatorname{Spin}(V_p)$; `hne`, `hopen`:
$\mathcal U_p$ is non-empty and open (subspace topology of the vector space topology `cliffordTopology` of $C(V_p)$); `hcof`:
$\mathcal U_p = \operatorname{Spin}(\Lambda_p)$ (`intSpin` of `baseChangeLat ℚ_[p] ℤ_[p] Λ`) for all but finitely many primes (7.3).
Conclusion: an element $u$ of $\operatorname{Spin}(V)$ whose image in $\operatorname{Spin}(V_p)$ (`spinBaseChange`) lies in $\mathcal U_p$ for
every prime $p$ (7.4). -/
@[kb "cassels1978" "Ch. 10, Thm. 7.1, p. 186"]
structure SpinStrongApproximation : Prop where
  /-- Theorem 7.1 for every space, form, lattice and family of open sets. -/
  approx : ∀ (V : Type) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (Q : QuadraticForm ℚ V),
    3 ≤ Module.finrank ℚ V → (QuadraticMap.associated Q).Nondegenerate →
    (∃ x : ℝ ⊗[ℚ] V, x ≠ 0 ∧ Q.baseChange ℝ x = 0) →
    ∀ (Λ : Submodule ℤ V), Λ.FG → Submodule.span ℚ (Λ : Set V) = ⊤ →
    ∀ (U : ∀ (p : ℕ) [Fact p.Prime], Set (spinGroup (Q.baseChange ℚ_[p]))),
      (∀ (p : ℕ) [Fact p.Prime], (U p).Nonempty) →
      (∀ (p : ℕ) [Fact p.Prime],
        @IsOpen _ (@instTopologicalSpaceSubtype _ _ (cliffordTopology (Q.baseChange ℚ_[p]))) (U p)) →
      {p : ℕ | ∃ hp : p.Prime, haveI : Fact p.Prime := ⟨hp⟩;
        U p ≠ (intSpin (Q := Q.baseChange ℚ_[p]) (baseChangeLat ℚ_[p] ℤ_[p] Λ) : Set _)}.Finite →
      ∃ u : spinGroup Q, ∀ (p : ℕ) [Fact p.Prime], spinBaseChange ℚ_[p] Q u ∈ U p

end QuadFormsKB.Cassels
