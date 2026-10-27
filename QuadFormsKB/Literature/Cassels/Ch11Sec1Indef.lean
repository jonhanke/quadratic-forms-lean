/-
# Cassels, Chapter 11, Theorem 1.4: one proper class in each spinor genus of an indefinite space

**Layer:** $V = F^n$ over a number field $F$ with the form $Q$ = `Q : QuadForm F n` (Cassels: $F = \mathbb Q$);
lattices `Lat F n`; proper classes `IsProperIsometric` and proper spinor genera `SameProperSpinorGenus`
(`Literature/OMeara/Sec102.lean`; Cassels' spinor genus is the proper spinor genus, `Ch11Sec1.lean`).

**Proves** Cassels' Theorem 1.4 (p. 202) for the proper classes, as Cassels states it: *for indefinite $V$ of
dimension $n \ge 3$, every spinor genus contains precisely one proper equivalence class*
(`isProperIsometric_of_sameProperSpinorGenus`, `properSpinorGenus_eq_properClass`). Cassels' proof, followed here:
if $\Gamma_p = \gamma\delta_p\Lambda_p$ with $\gamma \in O^+(V)$ and $\delta_p$ in the spinor kernel, strong
approximation (Cassels, Ch. 10, Thm. 7.1, Cor.; here `strongApproximationSpin`, unconditional) gives $\alpha$ in the
spinor kernel of $O(V)$ with $\alpha^{-1}\delta_p \in O(\Lambda_p)$ for all $p$, so $\Gamma = \gamma\alpha\Lambda$ with
$\gamma\alpha \in O^+(V)$.
-/
import QuadFormsKB.Literature.OMeara.Sec102
import QuadFormsKB.Lattices.SAVectorsAnisotropic

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-- **Cassels, Theorem 1.4** (Ch. 11, p. 202): *let $V, \phi$ be an indefinite quadratic space of dimension
$n \ge 3$. Then every spinor genus contains precisely one proper equivalence class*: two lattices in the same (proper)
spinor genus are properly equivalent. Over a number field $F$, with $V$ indefinite (isotropic at some infinite
place, `IsIndefinite`). -/
@[kb "cassels1978" "Ch. 11, Thm. 1.4, p. 202 (over a number field)"]
theorem isProperIsometric_of_sameProperSpinorGenus (hn : 3 ≤ n) (hQ : Q.Nondegenerate) (hind : IsIndefinite Q)
    {L M : Lat F n} (h : SameProperSpinorGenus Q L M) : IsProperIsometric Q L.1 M.1 := by
  let _ : MulAction (OAf Q) (Lat F n) := latAction Q
  obtain ⟨σ, hσ, k, hk, rfl⟩ := (sameProperSpinorGenus_iff Q).mp h
  obtain ⟨γ, hγ, hγL⟩ := strongApproximationSpin.approx Q hn hQ hind L k hk
  have hkL : latSMul Q k L = latSMul Q (diagF Q γ) L := by
    have hs : ((diagF Q γ)⁻¹ * k) • L = L :=
      MulAction.mem_stabilizer_iff.mp ((stabilizer_eq_locStab Q L).symm ▸ hγL)
    calc latSMul Q k L = (diagF Q γ * ((diagF Q γ)⁻¹ * k)) • L := by rw [mul_inv_cancel_left]; rfl
      _ = latSMul Q (diagF Q γ) L := by rw [mul_smul, hs]; rfl
  refine ⟨σ * γ, (Tamagawa.soSub Q F).mul_mem hσ (spinorKernel_le_soSub Q F hγ), ?_⟩
  rw [hkL, diagF_smul, diagF_smul, Lat.image, Lat.image, Subgroup.coe_mul, glImage_mul]

/-- **Cassels, Theorem 1.4** (Ch. 11, p. 202), as an equality of sets: for indefinite $V$ of dimension $n \ge 3$ the
(proper) spinor genus of $L$ is the proper class of $L$. -/
@[kb "cassels1978" "Ch. 11, Thm. 1.4, p. 202 (over a number field)"]
theorem properSpinorGenus_eq_properClass (hn : 3 ≤ n) (hQ : Q.Nondegenerate) (hind : IsIndefinite Q)
    (L : Lat F n) :
    {M : Lat F n | SameProperSpinorGenus Q L M} = {M : Lat F n | IsProperIsometric Q L.1 M.1} :=
  Set.Subset.antisymm (fun _ h => isProperIsometric_of_sameProperSpinorGenus Q hn hQ hind h)
    (fun _ h => IsProperIsometric.sameProperSpinorGenus Q h)

end QuadFormsKB.Lattices
