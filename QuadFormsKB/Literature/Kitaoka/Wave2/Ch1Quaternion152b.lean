/-
# Kitaoka 1993, Proposition 1.5.2: (iii) $\Rightarrow$ (i) and the full equivalence

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §1.5, Proposition 1.5.2, p. 25 (printed page).

**Proves**
* `proposition152_iii_i`: if $(C, N)^0 \cong (D, N)^0$ ($C = (\alpha,\beta)$, $D = (\gamma,\delta)$, $\operatorname{char} F \ne 2$,
  all parameters nonzero) then $C \cong D$ as $F$-algebras;
* `proposition152`: the statement `Proposition152` (unconditional).

*Proof of (iii) $\Rightarrow$ (i).* An isometry $\psi$ of the pure parts sends the generators $i, j$ of $C$ to pure
$u, v \in D$ with $N(u) = -\alpha$, $N(v) = -\beta$, orthogonal for the polar form. For pure $u$, $u^2 = -N(u)$, so
$u^2 = \alpha$, $v^2 = \beta$, and orthogonality of pure quaternions gives $uv = -vu$. Hence
$i \mapsto u$, $j \mapsto v$, $k \mapsto uv$ defines an $F$-algebra homomorphism $\varphi : C \to D$
(`QuaternionAlgebra.Basis.liftHom`), mapping pure quaternions to pure ones. As in (i) $\Rightarrow$ (ii), $\varphi$
preserves $N$; since the polar form of $N$ is nondegenerate, $\varphi$ is injective, and since
$\dim C = \dim D = 4$ it is bijective.
-/
import QuadFormsKB.Literature.Kitaoka.Wave2.Ch1Quaternion152

open QuadraticMap Quaternion

noncomputable section

namespace QuadFormsKB.Kitaoka

section Quaternion152b

variable {F : Type} [Field F]

/-- $(C, N)^0$ in coordinates: $-\alpha x_0^2 - \beta x_1^2 + \alpha\beta x_2^2$. -/
theorem quatNormPure_apply (α β : F) (x : Fin 3 → F) :
    quatNormPure α β x = -α * x 0 ^ 2 - β * x 1 ^ 2 + α * β * x 2 ^ 2 := by
  simp [quatNormPure, weightedSumSquares_apply, Fin.sum_univ_three]
  ring

/-- An isometry of pure parts yields a quaternion basis of $D$ of type $(\alpha, 0, \beta)$ with pure
generators. -/
theorem exists_pure_basis (h2 : (2 : F) ≠ 0) (α β γ δ : F)
    (h : (quatNormPure α β).Equivalent (quatNormPure γ δ)) :
    ∃ B : QuaternionAlgebra.Basis ℍ[F,γ,δ] α 0 β, B.i.re = 0 ∧ B.j.re = 0 ∧ B.k.re = 0 := by
  obtain ⟨ψ⟩ := h
  set a : Fin 3 → F := ψ (Pi.single 0 1) with ha
  set b : Fin 3 → F := ψ (Pi.single 1 1) with hb
  have hQa : -γ * a 0 ^ 2 - δ * a 1 ^ 2 + γ * δ * a 2 ^ 2 = -α := by
    have := ψ.map_app (Pi.single 0 1)
    rw [quatNormPure_apply, quatNormPure_apply] at this
    simpa using this
  have hQb : -γ * b 0 ^ 2 - δ * b 1 ^ 2 + γ * δ * b 2 ^ 2 = -β := by
    have := ψ.map_app (Pi.single 1 1)
    rw [quatNormPure_apply, quatNormPure_apply] at this
    simpa using this
  have hab : -γ * (a 0 + b 0) ^ 2 - δ * (a 1 + b 1) ^ 2 + γ * δ * (a 2 + b 2) ^ 2 = -α - β := by
    have := ψ.map_app (Pi.single 0 1 + Pi.single 1 1)
    rw [quatNormPure_apply, quatNormPure_apply, map_add] at this
    simp at this
    linear_combination this
  have hc2 : 2 * (-γ * a 0 * b 0 - δ * a 1 * b 1 + γ * δ * a 2 * b 2) = 0 := by
    linear_combination hab - hQa - hQb
  have hc : -γ * a 0 * b 0 - δ * a 1 * b 1 + γ * δ * a 2 * b 2 = 0 :=
    (mul_eq_zero.1 hc2).resolve_left h2
  let u : ℍ[F,γ,δ] := ⟨0, a 0, a 1, a 2⟩
  let v : ℍ[F,γ,δ] := ⟨0, b 0, b 1, b 2⟩
  have huu : u * u = α • (1 : ℍ[F,γ,δ]) + (0 : F) • u := by
    ext <;> simp [u] <;> first | ring1 |linear_combination hQa | linear_combination (-1 : F) * hQa
  have hvv : v * v = β • (1 : ℍ[F,γ,δ]) := by
    ext <;> simp [v] <;> first | ring1 |linear_combination hQb | linear_combination (-1 : F) * hQb
  have hvu : v * u = (0 : F) • v - u * v := by
    ext <;> simp [u, v] <;> first | ring1 | linear_combination (-2 : F) * hc
  refine ⟨⟨u, v, u * v, huu, hvv, rfl, hvu⟩, rfl, rfl, ?_⟩
  simp [u, v]
  linear_combination (-1 : F) * hc

/-- A homomorphism sending pure quaternions to pure ones preserves the norm form. -/
theorem quatNorm_algHom {α β γ δ : F} (φ : ℍ[F,α,β] →ₐ[F] ℍ[F,γ,δ])
    (hpure : ∀ x : ℍ[F,α,β], x.re = 0 → (φ x).re = 0) (x : ℍ[F,α,β]) :
    quatNorm γ δ (φ x) = quatNorm α β x := by
  set c := x.re with hc
  set p := x - algebraMap F ℍ[F,α,β] c with hpdef
  have hp : p.re = 0 := by simp [p, c]
  have hq : (φ p).re = 0 := hpure p hp
  have hxp : x = algebraMap F ℍ[F,α,β] c + p := by simp [p]
  have h1 : quatNorm α β x = c ^ 2 + quatNorm α β p := by
    rw [quatNorm_apply, quatNorm_apply]
    simp [p, c]
    ring
  have h3 : φ x = algebraMap F ℍ[F,γ,δ] c + φ p := by
    conv_lhs => rw [hxp]
    rw [map_add, AlgHom.commutes]
  have h4 : quatNorm γ δ (φ x) = c ^ 2 + quatNorm γ δ (φ p) := by
    rw [h3, quatNorm_apply, quatNorm_apply]
    simp [hq]
    ring
  have h5 : quatNorm γ δ (φ p) = quatNorm α β p := by
    have e1 := quatNorm_pure_sq γ δ (φ p) hq
    have e2 : φ p * φ p = algebraMap F _ (-(quatNorm α β p)) := by
      rw [← map_mul, quatNorm_pure_sq α β p hp, AlgHom.commutes]
    exact neg_inj.1 ((algebraMap F ℍ[F,γ,δ]).injective (e1.symm.trans e2))
  rw [h4, h5, h1]

/-- A norm-preserving algebra homomorphism of quaternion algebras is bijective
($\operatorname{char} F \ne 2$, $\alpha, \beta \ne 0$). -/
theorem algHom_bijective (h2 : (2 : F) ≠ 0) {α β γ δ : F} (hα : α ≠ 0) (hβ : β ≠ 0)
    (φ : ℍ[F,α,β] →ₐ[F] ℍ[F,γ,δ])
    (hN : ∀ x, quatNorm γ δ (φ x) = quatNorm α β x) : Function.Bijective φ := by
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have key : ∀ y, quatNorm α β (x + y) = quatNorm α β y := by
      intro y
      rw [← hN, ← hN y, map_add, hx, zero_add]
    have k0 := key 0
    have k1 := key ⟨1, 0, 0, 0⟩
    have k2 := key ⟨0, 1, 0, 0⟩
    have k3 := key ⟨0, 0, 1, 0⟩
    have k4 := key ⟨0, 0, 0, 1⟩
    simp only [quatNorm_apply] at k0 k1 k2 k3 k4
    simp at k0 k1 k2 k3 k4
    have e0 : x.re = 0 :=
      (mul_eq_zero.1 (by linear_combination k1 - k0 : 2 * x.re = 0)).resolve_left h2
    have e1 : x.imI = 0 := by
      have : (2 * α) * x.imI = 0 := by linear_combination -(k2 - k0)
      exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero h2 hα)
    have e2 : x.imJ = 0 := by
      have : (2 * β) * x.imJ = 0 := by linear_combination -(k3 - k0)
      exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero h2 hβ)
    have e3 : x.imK = 0 := by
      have : (2 * (α * β)) * x.imK = 0 := by linear_combination (k4 - k0)
      exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero h2 (mul_ne_zero hα hβ))
    ext <;> simp [e0, e1, e2, e3]
  refine ⟨hinj, ?_⟩
  have hsurj : Function.Surjective φ.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [QuaternionAlgebra.finrank_eq_four, QuaternionAlgebra.finrank_eq_four])).1 hinj
  exact hsurj

/-- **Kitaoka 1993, Proposition 1.5.2, (iii) $\Rightarrow$ (i)** (p. 25), *proved*: an isometry of the pure parts
$(C, N)^0 \cong (D, N)^0$ yields an $F$-algebra isomorphism $C \cong D$ (characteristic $\ne 2$, parameters nonzero;
the hypotheses on $\gamma, \delta$ are not used). -/
@[kb "kitaoka1993" "§1.5, Prop. 1.5.2, p. 25 ((iii) ⇒ (i))"]
theorem proposition152_iii_i (h2 : (2 : F) ≠ 0) (α β γ δ : F) (hα : α ≠ 0) (hβ : β ≠ 0)
    (h : (quatNormPure α β).Equivalent (quatNormPure γ δ)) :
    Nonempty (ℍ[F,α,β] ≃ₐ[F] ℍ[F,γ,δ]) := by
  obtain ⟨B, hi, hj, hk⟩ := exists_pure_basis h2 α β γ δ h
  have hpure : ∀ x : ℍ[F,α,β], x.re = 0 → (B.liftHom x).re = 0 := by
    intro x hx
    simp [QuaternionAlgebra.Basis.lift, hx, hi, hj, hk]
  exact ⟨AlgEquiv.ofBijective B.liftHom
    (algHom_bijective h2 hα hβ B.liftHom (quatNorm_algHom B.liftHom hpure))⟩

/-- **Kitaoka 1993, Proposition 1.5.2** (p. 25), *proved* (unconditional): (i) $\Leftrightarrow$ (ii)
$\Leftrightarrow$ (iii). -/
@[kb "kitaoka1993" "§1.5, Prop. 1.5.2, p. 25"]
theorem proposition152 : Proposition152 := by
  intro F _ h2 α β γ δ hα hβ hγ hδ
  tfae_have 1 → 2 := proposition152_i_ii h2 α β γ δ
  tfae_have 2 → 3 := proposition152_ii_iii h2 α β γ δ hα hβ hγ hδ
  tfae_have 3 → 1 := proposition152_iii_i h2 α β γ δ hα hβ
  tfae_finish

end Quaternion152b

end QuadFormsKB.Kitaoka
