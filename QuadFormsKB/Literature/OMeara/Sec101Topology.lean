/-
# O'Meara §101A: the topology of $V_\mathfrak p$ and of $O(V_\mathfrak p)$

**Layer:** $F$ a number field, $\mathfrak p$ (`v`) a finite spot, $F_\mathfrak p$ = `v.adicCompletion F` with its valuation
topology; $V_\mathfrak p = F_\mathfrak p^n$ and $L_F(V_\mathfrak p)$ = $n \times n$ matrices over $F_\mathfrak p$, with the
product topology (Mathlib); a form `Q : QuadForm F n`, symmetries `symm Q F_𝔭 x`.

**Proves** (standalone statements of facts the library used only inside proofs)
* `omeara101_r2` (§101A, pp. 286–287): $\det$ is continuous on $L_F(V_\mathfrak p)$, $GL(V_\mathfrak p)$ (the matrices with
  invertible determinant) is open, and inversion is continuous on it;
* `omeara101_2` (Example 101:2, p. 288): the anisotropic vectors form an open set and $u \mapsto \tau_u$ is continuous
  on it.
-/
import QuadFormsKB.Lattices.SAApprox

open NumberField IsDedekindDomain Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

/-- **$L_F(V)$ as a topological ring** (O'Meara 1973, §101A, pp. 286–287, over the completion $F_\mathfrak p$ at a finite
spot): $\det : L_F(V_\mathfrak p) \to F_\mathfrak p$ is continuous, the set of invertible matrices (O'Meara's $GL(V)$) is
open, and $\sigma \mapsto \sigma^{-1}$ is continuous on it. -/
@[kb "omeara1963" "§101A, pp. 286–287 (det continuous, GL(V) open, inversion continuous)"]
theorem omeara101_r2 :
    Continuous (fun M : Matrix (Fin n) (Fin n) Fv => M.det) ∧
      IsOpen {M : Matrix (Fin n) (Fin n) Fv | M.det ≠ 0} ∧
      ContinuousOn (fun M : Matrix (Fin n) (Fin n) Fv => M⁻¹) {M | M.det ≠ 0} := by
  have hdet : Continuous (fun M : Matrix (Fin n) (Fin n) Fv => M.det) := continuous_id.matrix_det
  refine ⟨hdet, isOpen_ne.preimage hdet, fun M hM => ?_⟩
  have hinv : ContinuousAt (fun M : Matrix (Fin n) (Fin n) Fv => (M.det)⁻¹ • M.adjugate) M :=
    (hdet.continuousAt.inv₀ hM).smul continuous_id.matrix_adjugate.continuousAt
  refine (hinv.congr ?_).continuousWithinAt
  filter_upwards with N
  rw [Matrix.inv_def, Ring.inverse_eq_inv']

/-- **Example 101:2** (O'Meara 1973, §101A, p. 288, at a finite spot): the set of anisotropic vectors
$\{u \in V_\mathfrak p : Q(u) \ne 0\}$ is open, and $u \mapsto \tau_u$ (the matrix of the symmetry, `symm`) is
continuous on it. -/
@[kb "omeara1963" "§101A, 101:2, p. 288"]
theorem omeara101_2 (Q : QuadForm F n) :
    IsOpen {u : Fin n → Fv | Q.evalIn Fv u ≠ 0} ∧
      ContinuousOn (fun u => ((symm Q Fv u : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv))
        {u | Q.evalIn Fv u ≠ 0} :=
  ⟨isOpen_ne.preimage (continuous_evalIn v Q), fun _ hu => (continuousAt_symm v Q hu).continuousWithinAt⟩

end QuadFormsKB.Lattices
