/-
# Kitaoka 1993, Proposition 1.5.2 on quaternion algebras (parts)

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §1.5, Proposition 1.5.2, p. 25 (printed page).

For $C = (\alpha, \beta)$, $D = (\gamma, \delta)$ with $\alpha,\beta,\gamma,\delta \in F^\times$, $\operatorname{char} F \ne 2$,
the statement `Proposition152` says that the following are equivalent: (i) $C \cong D$ as $F$-algebras; (ii)
$(C, N) \cong (D, N)$; (iii) $(C, N)^0 \cong (D, N)^0$.

**Proves**
* `quatNorm_equivalent_prod_pure`: $(C, N) \cong \langle 1\rangle \perp (C, N)^0$ (coordinates $(a_0; a_1, a_2, a_3)$);
* `proposition152_iii_ii`: (iii) $\Rightarrow$ (ii), by adding $\langle 1\rangle$;
* `proposition152_ii_iii`: (ii) $\Rightarrow$ (iii), by Witt cancellation of $\langle 1\rangle$
  (`QuadraticForm.equivalent_of_prod_equivalent_prod`);
* `proposition152_i_ii`: (i) $\Rightarrow$ (ii): an $F$-algebra isomorphism $\varphi$ preserves $N$.

**Not proved here.** (iii) $\Rightarrow$ (i) (and hence (ii) $\Rightarrow$ (i)), and the full `Proposition152`.

*Proof of (i) $\Rightarrow$ (ii).* For a pure $x$ (real part $0$), $x^2 = -N(x)\in F$. If $y = \varphi(x)$ has real part
$r \ne 0$, then $y^2$ scalar forces the imaginary part of $y$ to vanish (its components are $2r\cdot$ those of $y$), so
$y = r$ is a scalar, hence $x = \varphi^{-1}(r) = r$ is a scalar and pure, so $r = x.\mathrm{re} = 0$: contradiction. So $\varphi$
maps pure quaternions to pure quaternions, and then $N'(\varphi p) = -\varphi(p)^2 = -\varphi(p^2) = N(p)$ for pure $p$.
For general $x = c + p$, $N(x) = c^2 + N(p)$ on both sides.
-/
import QuadFormsKB.Literature.Kitaoka.Wave2.Ch1Quaternion
import QuadFormsKB.Witt.Cancellation

open QuadraticMap Quaternion

noncomputable section

namespace QuadFormsKB.Kitaoka

section Quaternion152

variable {F : Type} [Field F]

/-- The coordinate splitting $x \mapsto (a_0;\ a_1, a_2, a_3)$ of a quaternion. -/
def quatSplit (α β : F) : ℍ[F,α,β] ≃ₗ[F] (Fin 1 → F) × (Fin 3 → F) where
  toFun x := (fun _ => x.re, ![x.imI, x.imJ, x.imK])
  invFun p := ⟨p.1 0, p.2 0, p.2 1, p.2 2⟩
  map_add' x y := by
    ext i
    · simp
    · fin_cases i <;> simp
  map_smul' c x := by
    ext i
    · simp
    · fin_cases i <;> simp
  left_inv x := by ext <;> simp
  right_inv p := by
    ext i
    · fin_cases i; simp
    · fin_cases i <;> simp

/-- **$(C, N) \cong \langle 1\rangle \perp (C, N)^0$** (Kitaoka 1993, §1.5, p. 25). -/
theorem quatNorm_equivalent_prod_pure (α β : F) :
    (quatNorm α β).Equivalent ((weightedSumSquares F ![(1 : F)]).prod (quatNormPure α β)) := by
  refine ⟨{ toLinearEquiv := quatSplit α β, map_app' := ?_ }⟩
  intro x
  simp [quatSplit, quatNormPure, weightedSumSquares_apply, Fin.sum_univ_three, quatNorm_apply]
  ring

/-- **Kitaoka 1993, Proposition 1.5.2, (iii) $\Rightarrow$ (ii)** (p. 25), *proved*. -/
@[kb "kitaoka1993" "§1.5, Prop. 1.5.2, p. 25 ((iii) ⇒ (ii))"]
theorem proposition152_iii_ii (α β γ δ : F)
    (h : (quatNormPure α β).Equivalent (quatNormPure γ δ)) :
    (quatNorm α β).Equivalent (quatNorm γ δ) :=
  ((quatNorm_equivalent_prod_pure α β).trans
    (QuadraticMap.Equivalent.prod (QuadraticMap.Equivalent.refl _) h)).trans
    (quatNorm_equivalent_prod_pure γ δ).symm

/-- The one-dimensional form $\langle 1\rangle$ has nondegenerate polar form when $2 \ne 0$. -/
theorem weightedSumSquares_one_polar_nondegenerate (h2 : (2 : F) ≠ 0) :
    (polarBilin (weightedSumSquares F ![(1 : F)])).Nondegenerate := by
  rw [QuadraticForm.nondegenerate_polarBilin_iff]
  intro v hv
  have h : 2 * v 0 = 0 := by
    have := hv (fun _ => 1)
    simp [QuadraticMap.polar, weightedSumSquares_apply] at this
    linear_combination this
  have h0 : v 0 = 0 := (mul_eq_zero.1 h).resolve_left h2
  funext i
  fin_cases i
  simpa using h0

/-- **Kitaoka 1993, Proposition 1.5.2, (ii) $\Rightarrow$ (iii)** (p. 25), *proved*, by Witt cancellation of
$\langle 1\rangle$ (`QuadraticForm.equivalent_of_prod_equivalent_prod`). Characteristic $\ne 2$ makes
$\langle 1\rangle$ nonsingular; $\alpha, \beta \ne 0$ gives $(C, N)^0$ trivial radical. (The hypotheses on
$\gamma, \delta$ are not used.) -/
@[kb "kitaoka1993" "§1.5, Prop. 1.5.2, p. 25 ((ii) ⇒ (iii))"]
theorem proposition152_ii_iii (h2 : (2 : F) ≠ 0) (α β γ δ : F) (hα : α ≠ 0) (hβ : β ≠ 0)
    (_hγ : γ ≠ 0) (_hδ : δ ≠ 0)
    (h : (quatNorm α β).Equivalent (quatNorm γ δ)) :
    (quatNormPure α β).Equivalent (quatNormPure γ δ) := by
  have h' : ((weightedSumSquares F ![(1 : F)]).prod (quatNormPure α β)).Equivalent
      ((weightedSumSquares F ![(1 : F)]).prod (quatNormPure γ δ)) :=
    ((quatNorm_equivalent_prod_pure α β).symm.trans h).trans (quatNorm_equivalent_prod_pure γ δ)
  refine QuadraticForm.equivalent_of_prod_equivalent_prod
    (weightedSumSquares_one_polar_nondegenerate h2) ?_ h'
  have : NeZero (2 : F) := ⟨h2⟩
  rw [quatNormPure, QuadraticForm.radical_weightedSumSquares]
  have : {i : Fin 3 | ![-α, -β, α * β] i = 0} = ∅ := by
    ext i
    fin_cases i <;> simp [hα, hβ]
  rw [this, eq_bot_iff]
  intro v hv
  rw [Pi.mem_spanSubset_iff] at hv
  rw [Submodule.mem_bot]
  funext i
  exact hv i (by simp)

/-- A pure quaternion squares to the scalar $-N(x)$. -/
theorem quatNorm_pure_sq (α β : F) (x : ℍ[F,α,β]) (hx : x.re = 0) :
    x * x = algebraMap F ℍ[F,α,β] (-(quatNorm α β x)) := by
  obtain ⟨t, ht⟩ : ∃ t, t = -(quatNorm α β x) := ⟨_, rfl⟩
  rw [← ht]
  ext <;> simp [hx]
  all_goals first | ring1 | (rw [ht, quatNorm_apply, hx]; ring1)

/-- An $F$-algebra isomorphism of quaternion algebras maps pure quaternions to pure quaternions
($\operatorname{char} F \ne 2$). -/
theorem algEquiv_re_eq_zero (h2 : (2 : F) ≠ 0) {α β γ δ : F} (φ : ℍ[F,α,β] ≃ₐ[F] ℍ[F,γ,δ])
    (x : ℍ[F,α,β]) (hx : x.re = 0) : (φ x).re = 0 := by
  have hy : φ x * φ x = algebraMap F _ (-(quatNorm α β x)) := by
    rw [← map_mul, quatNorm_pure_sq α β x hx, AlgEquiv.commutes]
  have hI : (φ x * φ x).imI = (algebraMap F ℍ[F,γ,δ] (-(quatNorm α β x))).imI := by rw [hy]
  have hJ : (φ x * φ x).imJ = (algebraMap F ℍ[F,γ,δ] (-(quatNorm α β x))).imJ := by rw [hy]
  have hK : (φ x * φ x).imK = (algebraMap F ℍ[F,γ,δ] (-(quatNorm α β x))).imK := by rw [hy]
  simp at hI hJ hK
  by_contra hr
  have h2r : 2 * (φ x).re ≠ 0 := mul_ne_zero h2 hr
  have e1 : (φ x).imI = 0 := (mul_eq_zero.1 (by linear_combination hI : (2 * (φ x).re) * (φ x).imI = 0)).resolve_left h2r
  have e2 : (φ x).imJ = 0 := (mul_eq_zero.1 (by linear_combination hJ : (2 * (φ x).re) * (φ x).imJ = 0)).resolve_left h2r
  have e3 : (φ x).imK = 0 := (mul_eq_zero.1 (by linear_combination hK : (2 * (φ x).re) * (φ x).imK = 0)).resolve_left h2r
  have hs : φ x = algebraMap F ℍ[F,γ,δ] (φ x).re := by ext <;> simp [e1, e2, e3]
  have : x = algebraMap F ℍ[F,α,β] (φ x).re := by
    apply φ.injective
    rw [AlgEquiv.commutes]
    exact hs
  apply hr
  have := congrArg QuaternionAlgebra.re this
  simp [hx] at this
  exact this.symm

/-- An $F$-algebra isomorphism of quaternion algebras preserves the norm form. -/
theorem quatNorm_algEquiv (h2 : (2 : F) ≠ 0) {α β γ δ : F} (φ : ℍ[F,α,β] ≃ₐ[F] ℍ[F,γ,δ])
    (x : ℍ[F,α,β]) : quatNorm γ δ (φ x) = quatNorm α β x := by
  set c := x.re with hc
  set p := x - algebraMap F ℍ[F,α,β] c with hpdef
  have hp : p.re = 0 := by simp [p, c]
  have hq : (φ p).re = 0 := algEquiv_re_eq_zero h2 φ p hp
  have hxp : x = algebraMap F ℍ[F,α,β] c + p := by simp [p]
  have h1 : quatNorm α β x = c ^ 2 + quatNorm α β p := by
    rw [quatNorm_apply, quatNorm_apply]
    simp [p, c]
    ring
  have h3 : φ x = algebraMap F ℍ[F,γ,δ] c + φ p := by
    conv_lhs => rw [hxp]
    rw [map_add, AlgEquiv.commutes]
  have h4 : quatNorm γ δ (φ x) = c ^ 2 + quatNorm γ δ (φ p) := by
    rw [h3, quatNorm_apply, quatNorm_apply]
    simp [hq]
    ring
  have h5 : quatNorm γ δ (φ p) = quatNorm α β p := by
    have e1 := quatNorm_pure_sq γ δ (φ p) hq
    have e2 : φ p * φ p = algebraMap F _ (-(quatNorm α β p)) := by
      rw [← map_mul, quatNorm_pure_sq α β p hp, AlgEquiv.commutes]
    exact neg_inj.1 ((algebraMap F ℍ[F,γ,δ]).injective (e1.symm.trans e2))
  rw [h4, h5, h1]

/-- **Kitaoka 1993, Proposition 1.5.2, (i) $\Rightarrow$ (ii)** (p. 25), *proved*: isomorphic quaternion algebras
have isometric norm forms (characteristic $\ne 2$). -/
@[kb "kitaoka1993" "§1.5, Prop. 1.5.2, p. 25 ((i) ⇒ (ii))"]
theorem proposition152_i_ii (h2 : (2 : F) ≠ 0) (α β γ δ : F)
    (h : Nonempty (ℍ[F,α,β] ≃ₐ[F] ℍ[F,γ,δ])) :
    (quatNorm α β).Equivalent (quatNorm γ δ) := by
  obtain ⟨φ⟩ := h
  exact ⟨{ toLinearEquiv := φ.toLinearEquiv, map_app' := fun x => quatNorm_algEquiv h2 φ x }⟩

end Quaternion152

end QuadFormsKB.Kitaoka
