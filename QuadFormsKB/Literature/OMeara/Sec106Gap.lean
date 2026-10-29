/-
# O'Meara 106:1: an even unimodular lattice on $I_n$ exists if and only if $8 \mid n$

**Layer:** integer-valued forms `IntQF n` (a $\mathbb Z$-lattice with a chosen base), $Q(\vec x) =
\tfrac12\vec x^{\mathsf T}H\vec x$ with Hessian $H$ (`QuadForm.hessian`), positive definiteness `IntQF.PosDef`.

**Translation.** O'Meara's lattice $L = \mathbb Zx_0 + \dots + \mathbb Zx_{n-1}$ on a positive definite space has the
integral Gram matrix $G = (B(x_i, x_j))$, and $Q_{\mathrm{O'M}}(x) = B(x, x)$. $L$ is *even unimodular* when
$\det G = \pm 1$ and $Q_{\mathrm{O'M}}(L) \subseteq 2\mathbb Z$ (106.r3), i.e. $G$ is an even symmetric matrix with
$\det G = 1$ ($G$ is positive definite). This is exactly an `IntQF n` with Hessian $H = G$ and $\det H = 1$, positive
definite; the library's form is $Q = \tfrac12 Q_{\mathrm{O'M}}$. By 106.r1 (`omeara106_r1`, `Sec106A.lean`) every
positive definite space carrying a unimodular lattice is $I_n$, so "there is an even unimodular lattice on $I_n$" is the
existence of such a form.

**Proves** (O'Meara 1973, §106, p. 324) Proposition 106:1 (`omeara106_1`): there is a positive definite
`IntQF n` with $\det H = 1$ if and only if $8 \mid n$.

*Proof.* Not O'Meara's route (2-adic Hilbert symbols, 93:11, 93:18): "only if" is the library's theta-series argument
`Siegel.eight_dvd_of_posDef_det_one` (Serre, Ch. VII, §6.1); "if" is the orthogonal sum $E_8 \perp \dots \perp E_8$
(`Siegel.e8`, `Tamagawa.Frames.blockForm`).
-/
import QuadFormsKB.Siegel.EvenUnimodularRank
import QuadFormsKB.Siegel.E8
import QuadFormsKB.Tamagawa.BlockForm
import QuadFormsKB.Literature.Universal.Basic

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

open QuadFormsKB.Tamagawa.Frames

private lemma eval_zero_aux {n : ℕ} (Q : IntQF n) : Q.eval 0 = 0 := by
  simp [QuadForm.evalIn]

private lemma eval_nonneg_aux {n : ℕ} {Q : IntQF n} (hQ : Q.PosDef) (x : Fin n → ℤ) : 0 ≤ Q.eval x := by
  by_cases hx : x = 0
  · rw [hx, eval_zero_aux]
  · exact (hQ x hx).le

private lemma posDef_blockForm {r m : ℕ} {T : IntQF r} {Q' : IntQF m} (hT : T.PosDef) (hQ' : Q'.PosDef) :
    IntQF.PosDef (blockForm T Q') := by
  intro x hx
  have h := evalIn_blockForm ℤ T Q' x
  change (blockForm T Q').eval x = _ at h
  rw [h]
  by_cases h1 : (fun i => x (Fin.castAdd m i)) = 0
  · have h2 : (fun j => x (Fin.natAdd r j)) ≠ 0 := by
      intro h2
      apply hx
      funext i
      induction i using Fin.addCases with
      | left i => exact congrFun h1 i
      | right j => exact congrFun h2 j
    have := hQ' _ h2
    have := eval_nonneg_aux hT (fun i => x (Fin.castAdd m i))
    change 0 < T.eval _ + Q'.eval _
    omega
  · have := hT _ h1
    have := eval_nonneg_aux hQ' (fun j => x (Fin.natAdd r j))
    change 0 < T.eval _ + Q'.eval _
    omega

private lemma exists_even_unimodular (k : ℕ) : ∃ Q : IntQF (8 * k), Q.PosDef ∧ Q.hessian.det = 1 := by
  induction k with
  | zero =>
    refine ⟨QuadForm.diag (fun _ => 0), fun x hx => ?_, by simp⟩
    exact absurd (funext fun i => Fin.elim0 i) hx
  | succ k ih =>
    obtain ⟨Q, hQ, hdet⟩ := ih
    refine ⟨blockForm Q Siegel.e8, posDef_blockForm hQ Siegel.e8_posDef, ?_⟩
    rw [det_hessian_blockForm, hdet, Siegel.e8_det, one_mul]

/-- **Proposition 106:1** (O'Meara 1973, §106, p. 324): on the positive definite space $V \cong I_n$ over $\mathbb Q$
there is an even unimodular lattice if and only if $n \equiv 0 \bmod 8$. Stated for the lattice with a base: there is a
positive definite integer-valued form $Q$ in $n$ variables whose Hessian $H$ (O'Meara's Gram matrix $(B(x_i, x_j))$,
even on the diagonal) has $\det H = 1$ if and only if $8 \mid n$. (By 106.r1 such a lattice lies on $I_n$; see the
module docstring.) -/
@[kb "omeara1963" "§106, 106:1, p. 324"]
theorem omeara106_1 (n : ℕ) : (∃ Q : IntQF n, Q.PosDef ∧ Q.hessian.det = 1) ↔ 8 ∣ n := by
  constructor
  · rintro ⟨Q, hQ, hdet⟩
    exact Siegel.eight_dvd_of_posDef_det_one hQ hdet
  · rintro ⟨k, rfl⟩
    exact exists_even_unimodular k

end QuadFormsKB.Lattices
