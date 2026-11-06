/-
# Hanke, AWS 2009 notes, §3.4: Spin(V) as a double cover

J. Hanke, *Quadratic Forms and Automorphic Forms*, notes from the 2009 Arizona Winter School,
arXiv:1105.5759 v3 (bibkey `hanke2011aws`; PDF page = printed page), §3.4, p. 52.

Notation. A field $K$ with $2 \ne 0$ (`Invertible (2 : K)`), a finite-dimensional nondegenerate quadratic space
$(V, Q)$; $\mathrm{Spin}(V)$ = `spinGroup Q`; $\varphi(u)(\vec v) = u\vec v u^{-1}$ = `Cassels.spinConj`;
$SO(V)$ = `OMeara.orthPlus Q`; the spinor kernel $\kappa(V)$ (the rotations of trivial spinor norm) =
`OMeara.orthPrime Q`. The spinor norm $\mathrm{sn}(\sigma) = c(K^\times)^2$ is `OMeara.HasSpinorNorm Q σ c`.
-/
import QuadFormsKB.Literature.Cassels.Ch10.SpinGroup

namespace QuadFormsKB.AWS.Notes

open QuadFormsKB.OMeara QuadFormsKB.Cassels

variable {K V : Type*} [Field K] [Invertible (2 : K)] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

/-- **Notes, Thm 3.4.6, p. 52:** $\mathrm{Spin}(V)$ is a double covering of the spinor kernel
$\kappa(V) \subseteq SO(V)$: $\varphi : \mathrm{Spin}(V) \to SO(V)$ has image $\kappa(V)$, and $\varphi(u) = 1$
exactly for $u = \pm 1$, two distinct elements of $\mathrm{Spin}(V)$. The obstruction to $\varphi$ covering all of
$SO(V)$ is a rotation whose spinor norm is a nontrivial square class: the image is $SO(V)$ iff every
$\sigma \in SO(V)$ has spinor norm $(K^\times)^2$. ($V \ne 0$ is assumed, as the notes' $\mathrm{Spin}(V)$ is
built from anisotropic vectors.) -/
@[kb "hanke2011aws" "§3.4, Thm. 3.4.6, p. 52"]
theorem theorem_3_4_6 [Nontrivial V] (hQ : (QuadraticMap.associated Q).Nondegenerate) :
    (spinConj (Q := Q)).range = orthPrime Q ∧
      (∀ u : spinGroup Q, spinConj u = 1 ↔ (u : CliffordAlgebra Q) = 1 ∨ (u : CliffordAlgebra Q) = -1) ∧
      (1 : CliffordAlgebra Q) ≠ -1 ∧
      ((spinConj (Q := Q)).range = orthPlus Q ↔ ∀ σ ∈ orthPlus Q, HasSpinorNorm Q σ 1) := by
  refine ⟨range_spinConj hQ, spinConj_eq_one_iff hQ, ?_, ?_⟩
  · intro h
    have h2 : (2 : CliffordAlgebra Q) = 0 := by
      calc (2 : CliffordAlgebra Q) = 1 + 1 := one_add_one_eq_two.symm
        _ = -1 + 1 := by rw [← h]
        _ = 0 := neg_add_cancel 1
    have h2' : algebraMap K (CliffordAlgebra Q) 2 = 0 := by rw [map_ofNat]; exact h2
    have : (1 : CliffordAlgebra Q) = 0 := by
      calc (1 : CliffordAlgebra Q) = algebraMap K _ (⅟2 * 2) := by rw [invOf_mul_self, map_one]
        _ = 0 := by rw [map_mul, h2', mul_zero]
    exact one_ne_zero this
  · rw [range_spinConj hQ]
    constructor
    · intro h σ hσ
      rw [← h] at hσ
      exact hσ.2
    · intro h
      ext σ
      exact ⟨fun hσ => hσ.1, fun hσ => ⟨hσ, h σ hσ⟩⟩

/-- **Notes, Cor. 3.4.7, p. 52:** if $K^\times = (K^\times)^2$ (every nonzero element is a square, e.g. $K$
algebraically closed), then $\varphi : \mathrm{Spin}(V) \to SO(V)$ is onto, so $\mathrm{Spin}(V)$ is a double
cover of $SO(V)$ (kernel $\{\pm 1\}$ by `theorem_3_4_6`). -/
@[kb "hanke2011aws" "§3.4, Cor. 3.4.7, p. 52"]
theorem corollary_3_4_7 [Nontrivial V] (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hsq : ∀ c : K, c ≠ 0 → IsSquare c) : (spinConj (Q := Q)).range = orthPlus Q := by
  refine (theorem_3_4_6 hQ).2.2.2.2 fun σ hσ => ?_
  obtain ⟨c, hc, hσc⟩ := exists_hasSpinorNorm_of_mem_orth Q hQ (Subgroup.mem_inf.1 hσ).1
  obtain ⟨s, rfl⟩ := hsq c hc
  have hs : s ≠ 0 := by rintro rfl; simp at hc
  exact HasSpinorNorm.of_eq_mul_sq Q hσc (inv_ne_zero hs) (by field_simp)

/-- **Notes, §3.4, p. 52 (after Cor. 3.4.7):** for $K = \mathbb R$ and $(V, Q)$ positive definite, all spinor
norms are positive, hence $\kappa(V) = SO(V)$ and $\mathrm{Spin}(V)$ is again a double cover of $SO(V)$. -/
@[kb "hanke2011aws" "§3.4, p. 52 (K = ℝ, Q positive definite: κ(V) = SO(V))"]
theorem spinConj_range_real_posDef {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    [Nontrivial W] {P : QuadraticForm ℝ W} (hP : P.PosDef) :
    (spinConj (Q := P)).range = orthPlus P := by
  have hQ : (QuadraticMap.associated P).Nondegenerate :=
    (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
      (fun x y h => by rw [QuadraticMap.associated_isSymm ℝ P]; exact h)).2
      (QuadraticMap.separatingLeft_of_anisotropic P hP.anisotropic)
  refine (theorem_3_4_6 hQ).2.2.2.2 fun σ hσ => ?_
  obtain ⟨c, hc, l, hl, hσl, s, hs, hp⟩ := exists_hasSpinorNorm_of_mem_orth P hQ (Subgroup.mem_inf.1 hσ).1
  have hpos : 0 < (l.map P).prod := by
    refine List.prod_pos fun x hx => ?_
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hx
    exact hP u (fun h0 => hl u hu (by rw [h0, map_zero]))
  refine ⟨l, hl, hσl, Real.sqrt (l.map P).prod, (Real.sqrt_pos.2 hpos).ne', ?_⟩
  rw [one_mul, Real.sq_sqrt hpos.le]

end QuadFormsKB.AWS.Notes
