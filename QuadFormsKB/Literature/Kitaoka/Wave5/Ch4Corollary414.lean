/-
# Kitaoka 1993, Corollary 4.1.4: representations of rational spaces in codimension at least 3

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §4.1, Corollary 4.1.4, p. 67.

**Statement.** Let $U$ and $V$ be regular quadratic spaces over $\mathbb Q$ with $\dim V - \dim U \ge 3$. Then $U$ is
represented by $V$ ($U \to V$) as soon as $U_\infty = U \otimes \mathbb R$ is represented by
$V_\infty = V \otimes \mathbb R$.

**Proof** (Kitaoka's). At every prime $p$, $U_p \to V_p$ by Corollary 3.5.4 (`corollary354`, the case
$\dim V_p - \dim U_p \ge 3$); at the real place by hypothesis. The Hasse principle for representations
(Corollary 4.1.2, `isRepresentedBy_of_everywhere` with $F = \mathbb Q$) gives $U \to V$. The completions of $\mathbb Q$
as a number field are identified with $\mathbb R$ and $\mathbb Q_p$ by Mathlib's ring isomorphisms
(`InfinitePlace.Completion.ringEquivRealOfIsReal`, `Rat.HeightOneSpectrum.adicCompletion.padicEquiv`), along which
representations are transported (`isRepresentedBy_ringEquiv`).
-/
import QuadFormsKB.Literature.Kitaoka.Ch4HassePrinciple
import QuadFormsKB.Literature.Kitaoka.Wave2.Ch3Corollary354
import QuadFormsKB.Literature.Kitaoka.Wave3.Ch5Theorem523
import QuadFormsKB.Literature.Kitaoka.Wave5.Ch4RepTransport

open NumberField QuadraticMap

noncomputable section

namespace QuadFormsKB.Kitaoka

/-- In characteristic $0$, a nondegenerate polar form has a nondegenerate associated bilinear form. -/
theorem associated_nondegenerate_of_polarBilin {K V : Type*} [Field K] [CharZero K] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} (h : (QuadraticMap.polarBilin Q).Nondegenerate) :
    (QuadraticMap.associated Q).Nondegenerate := by
  rw [QuadraticForm.nondegenerate_polarBilin_iff] at h
  rw [LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    (LinearMap.IsSymm.isRefl (QuadraticForm.associated_isSymm K Q))]
  intro x hx
  apply h
  intro w
  have h0 := hx w
  rw [QuadraticMap.associated_apply] at h0
  rcases mul_eq_zero.mp h0 with h3 | h3
  · exact absurd h3 (by simp)
  · exact h3

/-- **Kitaoka 1993, Corollary 4.1.4** (p. 67): for regular quadratic spaces $U$, $V$ over $\mathbb Q$ (forms `QU`,
`QV` on $\mathbb Q^m$, $\mathbb Q^n$, nondegenerate) with $\dim V - \dim U \ge 3$ ($m + 3 \le n$), if $U_\infty$ is
represented by $V_\infty$ over $\mathbb R$, then $U$ is represented by $V$ over $\mathbb Q$. -/
@[kb "kitaoka1993" "§4.1, Cor. 4.1.4, p. 67"]
theorem corollary414 {m n : ℕ} (QU : RatQF m) (QV : RatQF n) (hU : QU.Nondegenerate) (hV : QV.Nondegenerate)
    (hmn : m + 3 ≤ n)
    (hR : OMeara.IsRepresentedBy (QU.toQuadraticFormIn ℝ) (QV.toQuadraticFormIn ℝ)) :
    OMeara.IsRepresentedBy (QU.toQuadraticFormIn ℚ) (QV.toQuadraticFormIn ℚ) := by
  refine isRepresentedBy_of_everywhere QU QV hU hV ?_
  intro v
  cases v with
  | infinite w =>
    exact isRepresentedBy_ringEquiv
      (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm QU QV hR
  | finite v =>
    have hp : Fact (Rat.HeightOneSpectrum.primesEquiv v : ℕ).Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
    have h1 := associated_nondegenerate_of_polarBilin (QuadForm.nondegenerate_polarBilin_toQuadraticFormIn
      (K := ℚ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)]) hU)
    have h2 := associated_nondegenerate_of_polarBilin (QuadForm.nondegenerate_polarBilin_toQuadraticFormIn
      (K := ℚ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)]) hV)
    have hloc := (corollary354 (Rat.HeightOneSpectrum.primesEquiv v : ℕ) m n _ _
      (discr'_ne_zero_of_nondegenerate _ _ h1) (discr'_ne_zero_of_nondegenerate _ _ h2)
      (by omega)).mpr (Or.inl (by omega))
    exact isRepresentedBy_adicCompletion_of_padic v QU QV hloc

end QuadFormsKB.Kitaoka
