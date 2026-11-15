/-
# Shimura 2004, Lemma 4.9: the spinor norm on $P^\varphi_m$

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), Lemma 4.9 (printed p. 34).

**Setting.** As in `Wave5/Levi.lean`, with $\varphi$ nondegenerate on $V$ and on $W$. For $\varepsilon \in
P^\varphi_m$ written as (4.6), $e = \pi^J(\varepsilon) \in SO^\omega(W)$ (`piJ_mem_orthPlus`) and
$d = \lambda^J(\varepsilon)$, the restriction of $\varepsilon$ to $J = I_m$.

**Proves** (unconditional; standard axioms only)
* $\pi^J(P^\varphi_m) \subseteq SO^\omega(W)$ (`piJ_mem_orthPlus`), from $P^\varphi_m = Q^\varphi R^\varphi$.

**States** (named proposition, not proved here)
* Lemma 4.9: $\sigma(\varepsilon) = \det(d)\,\sigma(e) \pmod{F^{\times 2}}$ (`Lemma4_9`). Its consequence
  $\sigma(R^\varphi) = 1$ is proved in `Wave5/Unipotent.lean` (`lemma_4_9_unipR`). By $P^\varphi_m = Q^\varphi
  R^\varphi$ the main formula reduces to the block-diagonal elements $\mathrm{diag}[\hat a, e, d]$; Shimura computes
  $\sigma$ of $\mathrm{diag}[\hat a, 1, d]$ through Proposition 4.8 (the lift $\ell_m$ of $GL_m$ into $G^+(V)$, in
  characteristic $0$), which is not formalized.
-/
import QuadFormsKB.Literature.Shimura2004.Wave5.Det
import QuadFormsKB.Citation

open Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.OMeara

namespace Levi

variable {F V : Type*} [Field F] [Invertible (2 : F)] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V} {m : ℕ} {e f : Fin m → V} (hH : IsHypFamily Q e f)
include hH

/-- $\pi^J(\varepsilon) \in SO^\omega(W)$ for $\varepsilon \in P^\varphi_m$ (Shimura p. 29: "$\varepsilon$ of (4.6)
belongs to $SO^\varphi$ if and only if $e \in SO^\omega$", the direction from $\varepsilon$ to $e$). -/
@[kb "shimura2004" "(4.6), p. 29 (ε ∈ SO^φ implies e ∈ SO^ω)"]
theorem piJ_mem_orthPlus {α : V ≃ₗ[F] V} (hα : α ∈ parabolicSO Q (spanE F e)) :
    piJ e f hH ⟨α, hα.1⟩ ∈ orthPlus (Q.restrict (wSpace Q e f)) := by
  obtain ⟨q, hq, r, hr, rfl⟩ := theorem_4_23 hH hα
  obtain ⟨hq', hqπ⟩ := (mem_leviQ_iff hH q).1 hq
  rw [unipR_eq_unipRO hH] at hr
  obtain ⟨hrP, _, hrπ⟩ := (mem_unipRO_iff hH r).1 hr
  have : (⟨q * r, hα.1⟩ : parabolicO Q (spanE F e)) = ⟨q, leviQO_le hq'⟩ * ⟨r, hrP⟩ := rfl
  rw [this, map_mul, hrπ, mul_one]
  exact hqπ

/-- **Lemma 4.9** (Shimura 2004, p. 34), main formula, as a named proposition (stated, not proved): for
$\varepsilon \in P^\varphi_m$ of the form (4.6), $\sigma(\varepsilon) = \det(d)\,\sigma(e)$ modulo $F^{\times 2}$, where
$d = \lambda^J(\varepsilon)$, $e = \pi^J(\varepsilon)$, and $\sigma$ is the spinor norm of $V$ (left) and of $W$
(right). The hypotheses `hQ`, `hW` are the nondegeneracy of $\varphi$ on $V$ and on $W$ under which both spinor
norms are defined. -/
@[kb "shimura2004" "Lemma 4.9, p. 34 (σ(ε) = det(d)σ(e) mod F^{×2})"]
def Lemma4_9 (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hW : (QuadraticMap.associated (Q.restrict (wSpace Q e f))).Nondegenerate) : Prop :=
  ∀ (α : V ≃ₗ[F] V) (hα : α ∈ parabolicSO Q (spanE F e)),
    spinorNormHom Q hQ ⟨α, hα.2⟩ =
      Lattices.SqClass.mk (LinearEquiv.det (lambdaJ (spanE F e) ⟨α, hα.1⟩)) *
        spinorNormHom (Q.restrict (wSpace Q e f)) hW ⟨piJ e f hH ⟨α, hα.1⟩, piJ_mem_orthPlus hH hα⟩

end Levi

end QuadFormsKB.Shimura2004
