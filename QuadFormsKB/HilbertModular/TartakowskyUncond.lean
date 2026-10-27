/-
# `LocalDensityGapNF` for rank $n \ge 5$, and Tartakowsky's theorem over $F$ unconditionally

**Theorems.**
* `LocalRankFive.isotropicIn_completion_of_five_le`: a nondegenerate form over $\mathcal O_F$ in $n \ge 5$ variables is isotropic over
  every non-archimedean completion $F_\mathfrak p$ (dyadic included), from the rank-$5$ case `LocalRankFive.isotropic_diag_five`
  (O'Meara 63:19; the repository's proof of `Quat.localRankFiveIsotropic`) after diagonalizing over $F_\mathfrak p$.
* `Siegel.localDensityGapNF_of_five_le`: the named input `Siegel.LocalDensityGapNF Q 𝔭` holds at **every** prime $\mathfrak p$ of
  $\mathcal O_F$ when $n \ge 5$ ($F$ any number field, $Q$ nondegenerate). This is the DVR theorem `DVR.exists_localDensity_gap`
  (strip $\varpi^2$, (5.11), $C'_\mathfrak p > 0$ at isotropic $\mathfrak p$, local constancy of $\beta_\mathfrak p$ and $C'_\mathfrak p$) at the
  completion $\mathfrak o_\mathfrak p$, with isotropy from the first item.
* `HilbertModular.tartakowsky_nf'` (**unconditional**): Hanke 2004, Thm 6.4 over a totally real $F$ with $h_F = 1$, for even
  $n \ge 6$, with a non-explicit constant.

All arguments are purely local (no global or Dirichlet-type input enters the lower bound for $\beta_\mathfrak p$).
-/
import QuadFormsKB.HilbertModular.Tartakowsky
import QuadFormsKB.Tamagawa.LocalRankFive
import QuadFormsKB.LocalDensity.DVRGap

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.LocalRankFive

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

local notation "Kv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **Forms of rank $n \ge 5$ over a non-archimedean completion are isotropic** (O'Meara 63:19; Serre 1973, Ch. IV, §2.2, Thm. 6,
Cor. 2 over $\mathbb Q_p$): for $Q$ nondegenerate over $\mathcal O_F$ in $n \ge 5$ variables and every prime $\mathfrak p$ (dyadic
included), $Q$ is isotropic over $F_\mathfrak p$. *Proof:* diagonalize $Q \otimes F_\mathfrak p \cong \langle a_0, \dots, a_{n-1}\rangle$
(`FieldGen.exists_isometric_diag`); $\langle a_0, \dots, a_4\rangle$ is isotropic (`isotropic_diag_five`), and so is the whole form
(`FieldGen.isotropicIn_diag_of_prefix`). -/
@[kb "omeara1963" "63:19 (n ≥ 5: isotropic over every non-archimedean completion) [unverified]"]
theorem isotropicIn_completion_of_five_le (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 5 ≤ n) :
    Q.IsotropicIn Kv := by
  classical
  set QK : QuadForm Kv n := (LocalDensity.NF.Qp v Q).map (algebraMap 𝔬 Kv) with hQK
  have hev : ∀ x : Fin n → Kv, QK.evalIn Kv x = Q.evalIn Kv x := fun x => by
    rw [← LocalDensity.NF.evalIn_Qp]
    simp [hQK, QuadForm.evalIn, QuadForm.map]
  have hnd : QK.Nondegenerate := by
    have h := LocalDensity.NF.nondegenerate_Qp v hQ
    have e : QK.hessian = (LocalDensity.NF.Qp v Q).hessian.map (algebraMap 𝔬 Kv) := by
      ext i j; simp [hQK, QuadForm.hessian, QuadForm.map]
    rw [QuadForm.Nondegenerate, e, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact fun h0 => h ((injective_iff_map_eq_zero _).mp (IsFractionRing.injective 𝔬 Kv) _ h0)
  obtain ⟨a, ha, hiso⟩ := FieldGen.exists_isometric_diag QK hnd
  have h1 : QK.IsotropicIn Kv := by
    rw [FieldGen.isotropicIn_iff_of_isometricIn Kv hiso]
    exact FieldGen.isotropicIn_diag_of_prefix Kv 5 hn a (isotropic_diag_five v _ fun _ => ha _)
  obtain ⟨x, hx, h0⟩ := h1
  exact ⟨x, hx, by rw [← hev]; exact h0⟩

end QuadFormsKB.LocalRankFive

namespace QuadFormsKB.Siegel

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- **`LocalDensityGapNF` holds at every prime for $n \ge 5$** (the local core of Hanke 2004, Thm 5.7(c), p. 373, over $F$): for $Q$
nondegenerate over $\mathcal O_F$ in $n \ge 5$ variables and every prime $\mathfrak p$ (in particular every $\mathfrak p \mid 2\det H$),
there is $c_\mathfrak p > 0$ with $\beta_\mathfrak p(m) \ge c_\mathfrak p$ for every $m \ne 0$ with $\beta_\mathfrak p(m) > 0$.
*Proof:* $\beta_\mathfrak p(m)$ is the density of $Q \otimes \mathfrak o_\mathfrak p$ at $\iota(m) \ne 0$ (`NF.localDensity_eq_completion`), and
`DVR.exists_localDensity_gap` applies since $Q$ is isotropic over $F_\mathfrak p$ (`isotropicIn_completion_of_five_le`). -/
@[kb "hanke2004" "Thm 5.7(c), p. 373 (local factor at every p, n ≥ 5: uniform lower bound, over F)"]
theorem localDensityGapNF_of_five_le (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 5 ≤ n)
    (v : HeightOneSpectrum (𝓞 F)) : LocalDensityGapNF Q v := by
  have hiso := (LocalDensity.NF.isotropicIn_Qp_iff v Q).2
    (LocalRankFive.isotropicIn_completion_of_five_le v Q hQ hn)
  obtain ⟨c, hc0, hc⟩ := LocalDensity.DVR.exists_localDensity_gap (v.adicCompletion F) (LocalDensity.NF.Qp v Q)
    (LocalDensity.NF.nondegenerate_Qp v hQ) (by omega) (LocalDensity.NF.π v) (LocalDensity.NF.irreducible_π v)
    (LocalDensity.NF.two_ne_zero' v) hiso
  refine ⟨⟨c, hc0, fun m hm hpos => ?_⟩⟩
  rw [LocalDensity.NF.localDensity_eq_completion] at hpos ⊢
  exact hc _ (LocalDensity.NF.ι_ne_zero v hm) hpos

end QuadFormsKB.Siegel

namespace QuadFormsKB.HilbertModular

open QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] [IsPrincipalIdealRing (𝓞 F)] {n : ℕ}

local notation "ιO" => algebraMap (𝓞 F) F

/-- **Tartakowsky's theorem over a totally real field with $h_F = 1$, even rank $n \ge 6$, unconditional** (Hanke 2004, Thm 6.4,
p. 382, $n$ even, over $F$; Tartakowsky 1929 over $\mathbb Q$). Let $F$ be totally real with $\mathcal O_F$ a PID and $Q_0$ a totally
positive definite quadratic form over $\mathcal O_F$ in an even number $n \ge 6$ of variables. There is $M_0$ such that every totally
positive $\nu \in \mathcal O_F$ that is locally represented at every prime $\mathfrak p$ and has $|N_{F/\mathbb Q}(\nu)| \ge M_0$ is
represented by $Q_0$ over $\mathcal O_F$:
$$\exists M_0\ \forall \nu \gg 0:\ \big(\forall \mathfrak p,\ \nu \text{ loc. rep. at } \mathfrak p\big) \wedge |N(\nu)| \ge M_0 \Rightarrow
  \exists x \in \mathcal O_F^n,\ Q_0(x) = \nu.$$
No inputs: `tartakowsky_nf` with `Siegel.LocalDensityGapNF` discharged at every prime (`Siegel.localDensityGapNF_of_five_le`).
For $n \ge 5$ every $\mathfrak p$ is isotropic, so Hanke's condition on the anisotropic primes is vacuous. $M_0$ exists but is not
explicit (Hecke's constant). -/
@[kb "hanke2004" "Thm 6.4, p. 382 (n even ≥ 6), over F with h_F = 1: unconditional, non-explicit constant (Tartakowsky)"]
theorem tartakowsky_nf' {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) (hn : 6 ≤ n) (heven : Even n) :
    ∃ M₀ : ℝ, ∀ ν : 𝓞 F, (∀ v, 0 < realEmb F v (ιO ν)) →
      (∀ v, LocalDensity.NF.IsLocallyRepresentedAt v Q₀ ν) →
      M₀ ≤ |((Algebra.norm ℚ (ιO ν) : ℚ) : ℝ)| → ∃ x : Fin n → 𝓞 F, Q₀.eval x = ν := by
  obtain ⟨k, hk⟩ := heven
  exact tartakowsky_nf hQ (k := k) (by omega) (by omega) fun v _ =>
    Siegel.localDensityGapNF_of_five_le Q₀ (det_hessian_ne_zero (isTotPosGram_Q₀ hQ)) (by omega) v

end QuadFormsKB.HilbertModular
