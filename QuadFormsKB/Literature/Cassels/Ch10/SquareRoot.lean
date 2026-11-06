/-
# Cassels, Chapter 10, §5: squaring has a local continuous cross-section over a complete valued field

**Source** (Cassels, *Rational Quadratic Forms*, Ch. 10, note after Lemma 5.1, Corollary 2, p. 185). Corollary 2 is
conditional on the squaring map $b \mapsto b^2$, $k^\times \to k^\times$, having locally a continuous cross-section. Cassels
remarks that this is clear for $k = \mathbb Q_p$ and $k = \mathbb R$, and indeed for every field complete with respect to
a valuation, the topology being the one given by the valuation.

**Formalized.** For a complete nontrivially normed field $k$ with $2 \ne 0$ and $b \ne 0$: a neighbourhood $W$ of $b^2$ and
a map $r$ continuous on $W$ with $r(b^2) = b$ and $r(d)^2 = d$ on $W$ (`exists_local_sqrt`), by the inverse function
theorem for the strictly differentiable map $x \mapsto x^2$ (derivative $2b \ne 0$ at $b$). Specializations to
$\mathbb Q_p$ (every prime $p$, including $p = 2$) and $\mathbb R$. Then Corollary 2 without hypothesis on squaring
(`exists_continuous_local_section_spin_of_complete`). Indices: not applicable.
-/
import QuadFormsKB.Literature.Cassels.Ch10.Sec5
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.NumberTheory.Padics.PadicNumbers

open Topology Module CliffordAlgebra

namespace QuadFormsKB.Cassels

/-- **Local continuous square root over a complete valued field** (Cassels, Ch. 10, note after Lemma 5.1, Cor. 2,
p. 185). Let $k$ be a complete nontrivially normed field with $2 \ne 0$ (`h2`) and $b \in k$ nonzero (`hb`). Then there
are a neighbourhood $W$ of $b^2$ and a map $r : k \to k$, continuous on $W$, with $r(b^2) = b$ and $r(d)^2 = d$ for all
$d \in W$. -/
@[kb "cassels1978" "Ch. 10, Lemma 5.1, Cor. 2, Note, p. 185 (squaring has a local continuous cross-section over a complete valued field)"]
theorem exists_local_sqrt {k : Type*} [NontriviallyNormedField k] [CompleteSpace k] (h2 : (2 : k) ≠ 0)
    {b : k} (hb : b ≠ 0) :
    ∃ W : Set k, W ∈ 𝓝 (b ^ 2) ∧ ∃ r : k → k, ContinuousOn r W ∧ r (b ^ 2) = b ∧
      ∀ d ∈ W, r d ^ 2 = d := by
  have hc : (2 * b : k) ≠ 0 := mul_ne_zero h2 hb
  have hd : HasStrictDerivAt (fun x : k => x ^ 2) (2 * b) b := by
    simpa using hasStrictDerivAt_pow 2 b
  have hf := hd.hasStrictFDerivAt_equiv hc
  set φ := hf.toOpenPartialHomeomorph (fun x : k => x ^ 2) with hφ
  have hco : (φ : k → k) = fun x : k => x ^ 2 := rfl
  have hmem : φ.target ∈ 𝓝 (b ^ 2) := by
    have := hf.image_mem_toOpenPartialHomeomorph_target
    exact φ.open_target.mem_nhds this
  refine ⟨φ.target, hmem, φ.symm, φ.continuousOn_symm, ?_, fun d hd' => ?_⟩
  · have := hf.toOpenPartialHomeomorph_coe
    have hsrc : b ∈ φ.source := hf.mem_toOpenPartialHomeomorph_source
    have h := φ.left_inv hsrc
    rwa [hco] at h
  · have := φ.right_inv hd'
    rwa [hco] at this

/-- **Local continuous square root in $\mathbb Q_p$** (every prime $p$, including $p = 2$): Cassels, Ch. 10, note after
Lemma 5.1, Cor. 2, p. 185. For $b \ne 0$ in $\mathbb Q_p$ there are a neighbourhood $W$ of $b^2$ and a map $r$
continuous on $W$ with $r(b^2) = b$ and $r(d)^2 = d$ on $W$. -/
@[kb "cassels1978" "Ch. 10, Lemma 5.1, Cor. 2, Note, p. 185 (squaring has a local continuous cross-section over a complete valued field) (ℚ_p and ℝ)"]
theorem exists_local_sqrt_padic (p : ℕ) [Fact p.Prime] {b : ℚ_[p]} (hb : b ≠ 0) :
    ∃ W : Set ℚ_[p], W ∈ 𝓝 (b ^ 2) ∧ ∃ r : ℚ_[p] → ℚ_[p], ContinuousOn r W ∧ r (b ^ 2) = b ∧
      ∀ d ∈ W, r d ^ 2 = d :=
  exists_local_sqrt (by norm_num) hb

/-- **Local continuous square root in $\mathbb R$**: Cassels, Ch. 10, note after Lemma 5.1, Cor. 2, p. 185. For
$b \ne 0$ real there are a neighbourhood $W$ of $b^2$ and a map $r$ continuous on $W$ with $r(b^2) = b$ and
$r(d)^2 = d$ on $W$. -/
@[kb "cassels1978" "Ch. 10, Lemma 5.1, Cor. 2, Note, p. 185 (squaring has a local continuous cross-section over a complete valued field) (ℚ_p and ℝ)"]
theorem exists_local_sqrt_real {b : ℝ} (hb : b ≠ 0) :
    ∃ W : Set ℝ, W ∈ 𝓝 (b ^ 2) ∧ ∃ r : ℝ → ℝ, ContinuousOn r W ∧ r (b ^ 2) = b ∧
      ∀ d ∈ W, r d ^ 2 = d :=
  exists_local_sqrt (by norm_num) hb

section Spin

open QuadFormsKB.OMeara

variable {k : Type*} [NontriviallyNormedField k] [CompleteSpace k] [Invertible (2 : k)]
  {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V] {Q : QuadraticForm k V}
  [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul k V] [T2Space V]
  [TopologicalSpace (CliffordAlgebra Q)] [IsTopologicalAddGroup (CliffordAlgebra Q)]
  [ContinuousSMul k (CliffordAlgebra Q)] [T2Space (CliffordAlgebra Q)]
  [TopologicalSpace (Module.End k V)] [IsTopologicalAddGroup (Module.End k V)]
  [ContinuousSMul k (Module.End k V)] [T2Space (Module.End k V)]

/-- **Cassels, Ch. 10, Lemma 5.1, Corollary 2, unconditionally over a complete valued field** (p. 185). Let $k$ be a
complete nontrivially normed field of characteristic $\ne 2$ (for instance $\mathbb Q_p$ or $\mathbb R$), $V \ne 0$ a
regular finite-dimensional quadratic space (`hQ`) with Clifford algebra $C(V)$ and $\operatorname{End}_k(V)$ carrying
Hausdorff topological-vector-space topologies, and $w_0 \in \operatorname{Spin}(V)$. Then there are a map
$\chi : \operatorname{End}_k(V) \to C(V)$ and an open neighbourhood $U$ of $T_{w_0}$ such that $\chi$ is continuous on
$U$, $\chi(T_{w_0}) = w_0$, and every $\sigma \in \Theta \cap U$ equals $T_w$ for the spin element
$w = \chi(\sigma)$. No hypothesis on squaring is needed: the local square root comes from `exists_local_sqrt`. -/
@[kb "cassels1978" "Ch. 10, Lemma 5.1, Cor. 2, p. 185 (complete valued field)"]
theorem exists_continuous_local_section_spin_of_complete [Nontrivial V]
    (hQ : (QuadraticMap.associated Q).Nondegenerate) (w₀ : spinGroup Q) :
    ∃ χ : Module.End k V → CliffordAlgebra Q, ∃ U : Set (Module.End k V), IsOpen U ∧
      (spinConj w₀ : Module.End k V) ∈ U ∧ ContinuousOn χ U ∧
      χ (spinConj w₀ : Module.End k V) = (w₀ : CliffordAlgebra Q) ∧
      ∀ σ ∈ orthPrime Q, (σ : Module.End k V) ∈ U →
        ∃ w : spinGroup Q, (w : CliffordAlgebra Q) = χ σ ∧ spinConj w = σ := by
  obtain ⟨W, hW, r, hr, hr1, hrsq⟩ := exists_local_sqrt (k := k) (Invertible.ne_zero (2 : k))
    (one_ne_zero : (1 : k) ≠ 0)
  rw [one_pow] at hW hr1
  exact exists_continuous_local_section_spin hQ hW hr hr1 (fun d hd _ => hrsq d hd) w₀

end Spin

end QuadFormsKB.Cassels
