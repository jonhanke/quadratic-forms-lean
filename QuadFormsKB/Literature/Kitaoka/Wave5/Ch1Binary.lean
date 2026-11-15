/-
# Kitaoka 1993, Proposition 1.3.1, Corollaries 1.3.1, 1.3.2 and Lemma 1.3.2 (first assertion): binary spaces over $\mathbb F_q$

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §1.3, p. 12 (the norm form $(F', N)$), Proposition
1.3.1, Corollary 1.3.1, Corollary 1.3.2, p. 13, Lemma 1.3.2, p. 15 (printed pages).

**Setting.** $F = \mathbb F_q$ is a finite field and $F'$ "the" quadratic extension of $F$: any field $F'$ with an
$F$-algebra structure and $[F' : F] = 2$ (`Module.finrank F F' = 2`). $N = N_{F'/F}$ is `Algebra.norm F`. Kitaoka's
$(F', N)$ is the quadratic space $F'$ with the form $N$; a linear bijection $e : U \to F'$ with
$N(e(x)) = q(x)$ for all $x$ is an isometry $U \cong (F', N)$. Quadratic spaces are Mathlib quadratic forms, the
bilinear form is $b(x, y) = q(x+y) - q(x) - q(y)$ (`polarBilin`), regular means $b$ nondegenerate, $H$ is
`QuadraticForm.hyperbolicPlane F` and $H^k$ is `QuadraticForm.hyperbolicSpace F k`.

**Proves** (unconditional, every characteristic)
* `proposition131` (Proposition 1.3.1): a $2$-dimensional anisotropic space $U$ over $F$ is isometric to $(F', N)$;
  hence $U$ is regular and $q(U) = F$.
* `corollary131` (Corollary 1.3.1): a regular $2$-dimensional space over $F$ is a hyperbolic plane or an anisotropic
  space isometric to $(F', N)$.
* `corollary132` (Corollary 1.3.2): the orthogonal sum of two isometric regular $2$-dimensional spaces over $F$ is
  hyperbolic ($\cong H^2$).
* `lemma132_similitude` (Lemma 1.3.2, first assertion): for a regular space $U$ of even dimension and $t \in F^\times$
  there is a linear automorphism $f$ of $U$ with $q(f(x)) = t\,q(x)$.

**Proof of Proposition 1.3.1** (Kitaoka's). For a basis $u_1, u_2$ of $U$, $q(xu_1 + u_2) = q(u_1)x^2 + b(u_1,u_2)x +
q(u_2) \ne 0$ for $x \in F$, so $f = q(u_1)X^2 + b(u_1, u_2)X + q(u_2)$ has no root in $F$; it has a root $\alpha$ in
$F'$ (`FiniteField.nonempty_algHom_of_finrank_dvd` applied to `AdjoinRoot f`), the other root being $\alpha^{q}$, and
$q(x_1u_1 + x_2u_2) = q(u_1)\,N(x_1 - \alpha x_2)$ since $N(z) = z\,z^q$
(`FiniteField.algebraMap_norm_eq_prod_pow`). With $\beta \in F'$, $N(\beta) = q(u_1)$ (`FiniteField.norm_surjective`),
$x_1u_1 + x_2u_2 \mapsto \beta(x_1 - \alpha x_2)$ is an isometry onto $(F', N)$.
-/
import QuadFormsKB.Literature.Kitaoka.Wave5.Ch1Radical
import QuadFormsKB.Literature.Kitaoka.Wave5.Ch1Counting
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.RingTheory.AdjoinRoot
import QuadFormsKB.Witt.Cancellation

open QuadraticMap Module

noncomputable section

namespace QuadFormsKB.Kitaoka.Binary

variable {F : Type} [Field F] [Finite F]

open Polynomial

/-- A quadratic extension of a finite field is finite. -/
theorem finite_of_finrank_two {F' : Type*} [Field F'] [Algebra F F'] (hF' : finrank F F' = 2) : Finite F' := by
  have : FiniteDimensional F F' := Module.finite_of_finrank_pos (by omega)
  exact Module.finite_of_finite F

/-- The conjugation of a quadratic extension $F'/F$ of a finite field: an $F$-automorphism $\sigma \ne 1$ with
$\sigma^2 = 1$, $N(z) = z\,\sigma(z)$ and $\operatorname{tr}(z) = z + \sigma(z)$ (it is the Frobenius $z \mapsto z^q$). -/
theorem exists_conj {F' : Type*} [Field F'] [Algebra F F'] (hF' : finrank F F' = 2) :
    ∃ σ : F' ≃ₐ[F] F', σ ≠ 1 ∧ (∀ z, σ (σ z) = z) ∧
      (∀ z, algebraMap F F' (Algebra.norm F z) = z * σ z) ∧
      (∀ z, algebraMap F F' (Algebra.trace F F' z) = z + σ z) := by
  have : Fintype F := Fintype.ofFinite F
  have : Finite F' := finite_of_finrank_two hF'
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic F F'
  have hord : orderOf σ = 2 := (FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic F F').trans hF'
  have hσz : ∀ z, σ z = z ^ Fintype.card F := fun z => rfl
  refine ⟨σ, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [h, orderOf_one] at hord
    exact absurd hord (by norm_num)
  · intro z
    have h2 : σ ^ 2 = 1 := hord ▸ pow_orderOf_eq_one σ
    have := congrArg (fun g : F' ≃ₐ[F] F' => g z) h2
    simpa [pow_two] using this
  · intro z
    rw [FiniteField.algebraMap_norm_eq_prod_pow, hF', hσz, Nat.card_eq_fintype_card]
    simp [Finset.prod_range_succ]
  · intro z
    rw [FiniteField.algebraMap_trace_eq_sum_pow, hF', hσz, Nat.card_eq_fintype_card]
    simp [Finset.sum_range_succ]

/-- An isometry $e : (U, q) \cong (F', N)$ onto a quadratic extension of a finite field makes $U$ regular: the
bilinear form of $N$ is $(z, w) \mapsto \operatorname{tr}(z\,\sigma(w))$, and the trace is not identically zero. -/
theorem nondegenerate_of_normIsometry {U : Type*} [AddCommGroup U] [Module F U] {F' : Type*} [Field F']
    [Algebra F F'] (hF' : finrank F F' = 2) (Q : QuadraticForm F U) (e : U ≃ₗ[F] F')
    (he : ∀ x, Algebra.norm F (e x) = Q x) : (polarBilin Q).Nondegenerate := by
  obtain ⟨σ, hσ1, hσσ, hN, -⟩ := exists_conj (F := F) hF'
  have hinj := (algebraMap F F').injective
  have hpolar : ∀ x y, algebraMap F F' (polar Q x y) = e x * σ (e y) + e y * σ (e x) := by
    intro x y
    simp only [polar, map_sub, ← he, hN, map_add]
    ring
  -- the trace $t + \sigma(t)$ is not identically zero
  have htr : ∃ t : F', t + σ t ≠ 0 := by
    by_contra! h
    apply hσ1
    have h1 := h 1
    rw [map_one] at h1
    ext z
    have hz := h z
    have h2 : (2 : F') = 0 := by rw [← one_add_one_eq_two]; exact h1
    have : σ z = -z := eq_neg_of_add_eq_zero_right hz
    rw [this, AlgEquiv.one_apply]
    linear_combination (-z) * h2
  obtain ⟨t, ht⟩ := htr
  rw [QuadraticForm.nondegenerate_polarBilin_iff]
  intro x hx
  by_contra hx0
  have hz : e x ≠ 0 := fun h => hx0 (e.injective (h.trans (map_zero e).symm))
  have key := hx (e.symm (σ (t / e x)))
  have := hpolar x (e.symm (σ (t / e x)))
  rw [key, map_zero, e.apply_symm_apply, hσσ, ← map_mul, div_mul_cancel₀ t hz,
    mul_div_cancel₀ t hz] at this
  exact ht this.symm

/-- The heart of Proposition 1.3.1: a $2$-dimensional anisotropic space over a finite field is isometric to
$(F', N)$. -/
theorem exists_normIsometry {U : Type*} [AddCommGroup U] [Module F U] (hdim : finrank F U = 2)
    (Q : QuadraticForm F U) (hQ : Q.Anisotropic)
    (F' : Type*) [Field F'] [Algebra F F'] (hF' : finrank F F' = 2) :
    ∃ e : U ≃ₗ[F] F', ∀ x, Algebra.norm F (e x) = Q x := by
  classical
  have : FiniteDimensional F U := Module.finite_of_finrank_pos (by omega)
  have : FiniteDimensional F F' := Module.finite_of_finrank_pos (by omega)
  have : Finite F' := finite_of_finrank_two hF'
  obtain ⟨σ, hσ1, -, hN, -⟩ := exists_conj (F := F) hF'
  let b : Basis (Fin 2) F U := Module.finBasisOfFinrankEq F U hdim
  set a := Q (b 0) with ha_def
  set β := polar Q (b 0) (b 1) with hβ_def
  set c := Q (b 1) with hc_def
  have ha : a ≠ 0 := fun h => b.ne_zero 0 (hQ _ h)
  have hQx : ∀ x1 x2 : F, Q (x1 • b 0 + x2 • b 1) = a * x1 ^ 2 + β * x1 * x2 + c * x2 ^ 2 := by
    intro x1 x2
    rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul, polar_smul_left,
      polar_smul_right]
    simp only [smul_eq_mul, ← ha_def, ← hβ_def, ← hc_def]
    ring
  have hxdecomp : ∀ x : U, x = b.repr x 0 • b 0 + b.repr x 1 • b 1 := by
    intro x
    have := b.sum_repr x
    rw [Fin.sum_univ_two] at this
    exact this.symm
  -- the polynomial $f = aX^2 + \beta X + c$ has no root in $F$
  let f : F[X] := C a * X ^ 2 + C β * X + C c
  have hfeval : ∀ x : F, f.eval x = Q (x • b 0 + (1 : F) • b 1) := by
    intro x; rw [hQx]; simp [f]
  have hnoroot : ∀ x : F, f.eval x ≠ 0 := by
    intro x h
    rw [hfeval] at h
    have h0 := hQ _ h
    have hli := b.linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    have := hli ![x, 1] (by simpa [Fin.sum_univ_two] using h0) 1
    simp at this
  have hdeg : f.natDegree = 2 := by
    simp only [f]
    compute_degree!
  have hirr : Irreducible f :=
    irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) fun x => hnoroot x
  have : Fact (Irreducible f) := ⟨hirr⟩
  have hf0 : f ≠ 0 := hirr.ne_zero
  have : Module.Finite F (AdjoinRoot f) := (AdjoinRoot.powerBasis hf0).finite
  have hK : finrank F (AdjoinRoot f) = 2 := by
    rw [(AdjoinRoot.powerBasis hf0).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := F) (K := AdjoinRoot f) (L := F')
    (by rw [hK, hF'])
  set α := φ (AdjoinRoot.root f) with hα_def
  have hφs : Function.Surjective φ := by
    have hinj : Function.Injective φ.toLinearMap := φ.toRingHom.injective
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hK.trans hF'.symm)).mp hinj
  have hσα : σ α ≠ α := by
    intro h
    have hcomp : (σ.toAlgHom.comp φ) = φ := AdjoinRoot.algHom_ext (by simpa using h)
    apply hσ1
    ext z
    obtain ⟨w, rfl⟩ := hφs z
    simpa using AlgHom.congr_fun hcomp w
  have hroot : ∀ γ : F', aeval γ f = 0 →
      algebraMap F F' a * γ ^ 2 + algebraMap F F' β * γ + algebraMap F F' c = 0 := by
    intro γ hγ
    simpa [f] using hγ
  have hα : aeval α f = 0 := by
    rw [hα_def, aeval_algHom_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  have hα' : aeval (σ α) f = 0 := by
    rw [show σ α = σ.toAlgHom α from rfl, aeval_algHom_apply, hα, map_zero]
  have r1 := hroot α hα
  have r2 := hroot (σ α) hα'
  set A := algebraMap F F' a
  set B := algebraMap F F' β
  set Cc := algebraMap F F' c
  have hsum : A * (α + σ α) = -B := by
    have hne : α - σ α ≠ 0 := sub_ne_zero.mpr (Ne.symm hσα)
    apply mul_left_cancel₀ hne
    linear_combination r1 - r2
  have hprod : A * (α * σ α) = Cc := by linear_combination -r1 + α * hsum
  -- the isometry
  have hA0 : algebraMap F F' a ≠ 0 := by
    rw [map_ne_zero_iff _ (algebraMap F F').injective]; exact ha
  obtain ⟨γ, hγ⟩ := FiniteField.norm_surjective F F' a
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    rw [Algebra.norm_zero] at hγ
    exact ha hγ.symm
  let g : U →ₗ[F] F' := b.constr F ![γ, -(γ * α)]
  have hg : ∀ x1 x2 : F, g (x1 • b 0 + x2 • b 1) =
      γ * (algebraMap F F' x1 - α * algebraMap F F' x2) := by
    intro x1 x2
    simp only [map_add, map_smul, g, Basis.constr_basis, Matrix.cons_val_zero, Matrix.cons_val_one,
      Algebra.smul_def]
    ring
  have hginj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    rw [hxdecomp x, hg] at hx
    have h1 : algebraMap F F' (b.repr x 0) - α * algebraMap F F' (b.repr x 1) = 0 :=
      (mul_eq_zero.mp hx).resolve_left hγ0
    by_cases hx2 : b.repr x 1 = 0
    · simp only [hx2, map_zero, mul_zero, sub_zero] at h1
      rw [map_eq_zero_iff _ (algebraMap F F').injective] at h1
      rw [hxdecomp x, h1, hx2, zero_smul, zero_smul, add_zero]
    · exfalso
      have hαeq : α = algebraMap F F' (b.repr x 0 / b.repr x 1) := by
        rw [map_div₀]
        have : algebraMap F F' (b.repr x 1) ≠ 0 := by
          rw [map_ne_zero_iff _ (algebraMap F F').injective]; exact hx2
        field_simp
        linear_combination -h1
      apply hnoroot (b.repr x 0 / b.repr x 1)
      have hev : ∀ s : F, f.eval s = a * s ^ 2 + β * s + c := fun s => by simp [f]
      rw [hev]
      apply (algebraMap F F').injective
      have r1' := r1
      rw [hαeq] at r1'
      simpa [A, B, Cc, map_add, map_mul, map_pow] using r1'
  have hsurj : Function.Surjective g :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hdim.trans hF'.symm)).mp hginj
  refine ⟨LinearEquiv.ofBijective g ⟨hginj, hsurj⟩, fun x => ?_⟩
  have hγN : γ * σ γ = A := by rw [← hN, hγ]
  apply (algebraMap F F').injective
  show algebraMap F F' (Algebra.norm F (g x)) = _
  rw [hN, hxdecomp x, hg, hQx]
  simp only [map_mul, map_sub, map_add, map_pow, AlgEquiv.commutes]
  set X1 := algebraMap F F' (b.repr x 0)
  set X2 := algebraMap F F' (b.repr x 1)
  linear_combination (X1 ^ 2 - (α + σ α) * X1 * X2 + α * σ α * X2 ^ 2) * hγN - X1 * X2 * hsum +
    X2 ^ 2 * hprod

omit [Finite F] in
/-- An anisotropic plane over a finite field gives an irreducible quadratic polynomial
$q(u_1)X^2 + b(u_1, u_2)X + q(u_2)$. -/
theorem exists_irreducible_quadratic {U : Type*} [AddCommGroup U] [Module F U] (hdim : finrank F U = 2)
    (Q : QuadraticForm F U) (hQ : Q.Anisotropic) : ∃ f : F[X], Irreducible f ∧ f.natDegree = 2 := by
  classical
  have : FiniteDimensional F U := Module.finite_of_finrank_pos (by omega)
  let b : Basis (Fin 2) F U := Module.finBasisOfFinrankEq F U hdim
  let f : F[X] := C (Q (b 0)) * X ^ 2 + C (polar Q (b 0) (b 1)) * X + C (Q (b 1))
  have hnoroot : ∀ x : F, f.eval x ≠ 0 := by
    intro x h
    have hfe : f.eval x = Q (x • b 0 + (1 : F) • b 1) := by
      rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul, polar_smul_left,
        polar_smul_right]
      simp [f, smul_eq_mul]
      ring
    rw [hfe] at h
    have h0 := hQ _ h
    have hli := b.linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    have := hli ![x, 1] (by simpa [Fin.sum_univ_two] using h0) 1
    simp at this
  have hdeg : f.natDegree = 2 := by
    have ha : Q (b 0) ≠ 0 := fun h => b.ne_zero 0 (hQ _ h)
    simp only [f]
    compute_degree!
  exact ⟨f, irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) fun x => hnoroot x, hdeg⟩

omit [Finite F] in
/-- An anisotropic plane over a finite field $F$ gives a quadratic extension $F'$ of $F$ (`AdjoinRoot` of the
irreducible quadratic of `exists_irreducible_quadratic`). -/
theorem exists_quadExt_of_anisotropic {U : Type*} [AddCommGroup U] [Module F U] (hdim : finrank F U = 2)
    (Q : QuadraticForm F U) (hQ : Q.Anisotropic) :
    ∃ (F' : Type) (_ : Field F') (_ : Algebra F F'), finrank F F' = 2 := by
  obtain ⟨f, hirr, hdeg⟩ := exists_irreducible_quadratic hdim Q hQ
  have : Fact (Irreducible f) := ⟨hirr⟩
  have hf0 := hirr.ne_zero
  have : Module.Finite F (AdjoinRoot f) := (AdjoinRoot.powerBasis hf0).finite
  exact ⟨AdjoinRoot f, inferInstance, inferInstance, by
    rw [(AdjoinRoot.powerBasis hf0).finrank, AdjoinRoot.powerBasis_dim, hdeg]⟩

omit [Finite F] in
/-- A similitude with multiplier $t$ transports along an isometry. -/
theorem exists_similitude_of_equivalent {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W]
    [Module F W] {Q : QuadraticForm F V} {R : QuadraticForm F W} (h : Q.Equivalent R) {t : F}
    (hR : ∃ ψ : W ≃ₗ[F] W, ∀ y, R (ψ y) = t * R y) : ∃ φ : V ≃ₗ[F] V, ∀ x, Q (φ x) = t * Q x := by
  obtain ⟨e⟩ := h
  obtain ⟨ψ, hψ⟩ := hR
  have h1 : ∀ y, Q (e.symm y) = R y := fun y => by rw [← e.map_app (e.symm y), e.apply_symm_apply]
  refine ⟨e.toLinearEquiv.trans (ψ.trans e.toLinearEquiv.symm), fun x => ?_⟩
  show Q (e.symm (ψ (e x))) = _
  rw [h1, hψ, e.map_app]

omit [Finite F] in
/-- Similitudes of two forms with the same multiplier give a similitude of their orthogonal sum. -/
theorem exists_similitude_prod {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W]
    [Module F W] {Q : QuadraticForm F V} {R : QuadraticForm F W} {t : F}
    (hQ : ∃ φ : V ≃ₗ[F] V, ∀ x, Q (φ x) = t * Q x) (hR : ∃ ψ : W ≃ₗ[F] W, ∀ y, R (ψ y) = t * R y) :
    ∃ φ : (V × W) ≃ₗ[F] (V × W), ∀ x, (Q.prod R) (φ x) = t * (Q.prod R) x := by
  obtain ⟨φ, hφ⟩ := hQ
  obtain ⟨ψ, hψ⟩ := hR
  refine ⟨LinearEquiv.prodCongr φ ψ, fun x => ?_⟩
  simp only [LinearEquiv.prodCongr_apply, QuadraticMap.prod_apply, hφ, hψ]
  ring

omit [Finite F] in
/-- The hyperbolic space $H^k$ has a similitude with any multiplier $t \ne 0$:
$(x_i, y_i)_i \mapsto (x_i, t y_i)_i$. -/
theorem exists_similitude_hyperbolicSpace (k : ℕ) {t : F} (ht : t ≠ 0) :
    ∃ φ : (Fin k → F × F) ≃ₗ[F] (Fin k → F × F),
      ∀ x, QuadraticForm.hyperbolicSpace F k (φ x) = t * QuadraticForm.hyperbolicSpace F k x := by
  refine ⟨LinearEquiv.piCongrRight fun _ =>
    LinearEquiv.prodCongr (LinearEquiv.refl F F) (LinearEquiv.smulOfNeZero F F t ht), fun x => ?_⟩
  simp only [QuadraticForm.hyperbolicSpace_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [smul_eq_mul]
  ring

/-- **Kitaoka 1993, Proposition 1.3.1** (p. 13). Let $U$ be a $2$-dimensional anisotropic quadratic space over a
finite field $F$ and $F'$ a quadratic extension of $F$. Then $U \cong (F', N)$: there is a linear bijection
$e : U \to F'$ with $N_{F'/F}(e(x)) = q(x)$; hence $U$ is regular and $q(U) = F$. Unconditional. -/
@[kb "kitaoka1993" "§1.3, Prop. 1.3.1, p. 13"]
theorem proposition131 {U : Type*} [AddCommGroup U] [Module F U] (hdim : finrank F U = 2)
    (Q : QuadraticForm F U) (hQ : Q.Anisotropic)
    (F' : Type*) [Field F'] [Algebra F F'] (hF' : finrank F F' = 2) :
    (∃ e : U ≃ₗ[F] F', ∀ x, Algebra.norm F (e x) = Q x) ∧ (polarBilin Q).Nondegenerate ∧
      ∀ t : F, ∃ x, Q x = t := by
  classical
  obtain ⟨e, he⟩ := exists_normIsometry hdim Q hQ F' hF'
  refine ⟨⟨e, he⟩, ?_, ?_⟩
  · exact nondegenerate_of_normIsometry hF' Q e he
  · intro t
    have : Finite F' := finite_of_finrank_two hF'
    obtain ⟨w, hw⟩ := FiniteField.norm_surjective F F' t
    exact ⟨e.symm w, by rw [← he, e.apply_symm_apply, hw]⟩

/-- **Kitaoka 1993, Corollary 1.3.1** (p. 13). A regular $2$-dimensional quadratic space $U$ over a finite field $F$
is isometric to the hyperbolic plane, or is anisotropic and isometric to $(F', N)$ for a quadratic extension $F'$ of
$F$. Unconditional. -/
@[kb "kitaoka1993" "§1.3, Cor. 1.3.1, p. 13"]
theorem corollary131 {U : Type*} [AddCommGroup U] [Module F U] (hdim : finrank F U = 2)
    (Q : QuadraticForm F U) (hreg : (polarBilin Q).Nondegenerate)
    (F' : Type*) [Field F'] [Algebra F F'] (hF' : finrank F F' = 2) :
    Q.Equivalent (QuadraticForm.hyperbolicPlane F) ∨
      (Q.Anisotropic ∧ ∃ e : U ≃ₗ[F] F', ∀ x, Algebra.norm F (e x) = Q x) := by
  have : FiniteDimensional F U := Module.finite_of_finrank_pos (by omega)
  by_cases hA : Q.Anisotropic
  · exact Or.inr ⟨hA, exists_normIsometry hdim Q hA F' hF'⟩
  · left
    simp only [QuadraticMap.Anisotropic, not_forall] at hA
    obtain ⟨v, hv, hv0⟩ := hA
    exact Radical.proposition122_plane Q hdim hreg ⟨v, hv0, hv⟩

/-- An anisotropic plane over a finite field has a similitude with any multiplier $t \ne 0$: multiplication by an
element of norm $t$ in $(F', N)$. -/
theorem exists_similitude_of_anisotropic {U : Type*} [AddCommGroup U] [Module F U] (hdim : finrank F U = 2)
    (Q : QuadraticForm F U) (hQ : Q.Anisotropic) {t : F} (ht : t ≠ 0) :
    ∃ φ : U ≃ₗ[F] U, ∀ x, Q (φ x) = t * Q x := by
  obtain ⟨F', _, _, hF'⟩ := exists_quadExt_of_anisotropic hdim Q hQ
  have : Finite F' := finite_of_finrank_two hF'
  obtain ⟨e, he⟩ := exists_normIsometry hdim Q hQ F' hF'
  obtain ⟨k, hk⟩ := FiniteField.norm_surjective F F' t
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [Algebra.norm_zero] at hk
    exact ht hk.symm
  let m : F' ≃ₗ[F] F' := LinearEquiv.ofBijective (LinearMap.mulLeft F k)
    ⟨fun a b h => mul_left_cancel₀ hk0 h, fun z => ⟨k⁻¹ * z, by simp [hk0]⟩⟩
  refine ⟨e.trans (m.trans e.symm), fun x => ?_⟩
  rw [← he, ← he]
  show Algebra.norm F (e (e.symm (k * e x))) = _
  rw [e.apply_symm_apply, map_mul, hk]

/-- A regular plane over a finite field has a similitude with any multiplier $t \ne 0$. -/
theorem exists_similitude_of_plane {U : Type*} [AddCommGroup U] [Module F U] (hdim : finrank F U = 2)
    (Q : QuadraticForm F U) (hreg : (polarBilin Q).Nondegenerate) {t : F} (ht : t ≠ 0) :
    ∃ φ : U ≃ₗ[F] U, ∀ x, Q (φ x) = t * Q x := by
  have : FiniteDimensional F U := Module.finite_of_finrank_pos (by omega)
  by_cases hA : Q.Anisotropic
  · exact exists_similitude_of_anisotropic hdim Q hA ht
  · simp only [QuadraticMap.Anisotropic, not_forall] at hA
    obtain ⟨v, hv, hv0⟩ := hA
    have hH := Radical.proposition122_plane Q hdim hreg ⟨v, hv0, hv⟩
    refine exists_similitude_of_equivalent hH ⟨LinearEquiv.prodCongr (LinearEquiv.refl F F)
      (LinearEquiv.smulOfNeZero F F t ht), fun y => ?_⟩
    simp [smul_eq_mul]
    ring

/-- **Kitaoka 1993, Corollary 1.3.2** (p. 13). The orthogonal sum of two isometric regular $2$-dimensional quadratic
spaces over a finite field $F$ is a hyperbolic space, here $\cong H^2$. Unconditional. -/
@[kb "kitaoka1993" "§1.3, Cor. 1.3.2, p. 13"]
theorem corollary132 {U U' : Type*} [AddCommGroup U] [Module F U] [AddCommGroup U'] [Module F U']
    (hdim : finrank F U = 2) (Q : QuadraticForm F U) (Q' : QuadraticForm F U')
    (hreg : (polarBilin Q).Nondegenerate) (hQQ' : Q.Equivalent Q') :
    (Q.prod Q').Equivalent (QuadraticForm.hyperbolicSpace F 2) := by
  classical
  have : FiniteDimensional F U := Module.finite_of_finrank_pos (by omega)
  obtain ⟨g⟩ := hQQ'
  refine (QuadraticMap.Equivalent.prod (QuadraticMap.Equivalent.refl Q) ⟨g.symm⟩).trans ?_
  -- a totally isotropic plane in $U \perp U$: the graph of a similitude with multiplier $-1$
  obtain ⟨φ, hφ⟩ := exists_similitude_of_plane hdim Q hreg (t := -1) (by norm_num)
  let P := Q.prod Q
  let ι : U →ₗ[F] U × U := LinearMap.prod LinearMap.id φ.toLinearMap
  have hιinj : Function.Injective ι := fun x y h => congrArg Prod.fst h
  let V := LinearMap.range ι
  have hregP : (polarBilin P).Nondegenerate := QuadraticForm.nondegenerate_polarBilin_prod hreg hreg
  have hV : V ⊓ LinearMap.BilinForm.orthogonal (polarBilin P) ⊤ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨-, hx⟩
    rw [Submodule.mem_bot]
    apply (QuadraticForm.nondegenerate_polarBilin_iff P).mp hregP
    intro w
    have := hx w Submodule.mem_top
    rw [polar_comm]
    exact this
  have hiso : ∀ v ∈ V, P v = 0 := by
    rintro _ ⟨y, rfl⟩
    simp [P, ι, QuadraticMap.prod_apply, hφ]
  obtain ⟨W, -, hWdim, hdisj, hequiv⟩ := Radical.proposition122 P V hV hiso
  have hVdim : finrank F V = 2 := by
    rw [LinearMap.finrank_range_of_inj hιinj, hdim]
  have htop : V ⊔ W = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq V W
    rw [disjoint_iff.mp hdisj, finrank_bot, add_zero] at h1
    rw [h1, hWdim, hVdim, Module.finrank_prod, hdim]
  rw [htop, hVdim] at hequiv
  refine QuadraticMap.Equivalent.trans ?_ hequiv
  exact ⟨{ toLinearEquiv := (LinearEquiv.ofTop ⊤ rfl).symm, map_app' := fun x => rfl }⟩

/-- **Kitaoka 1993, Lemma 1.3.2, first assertion** (p. 15). For a regular quadratic space $U$ of even dimension $u$
over a finite field $F$ and $t \in F^\times$ there is a linear automorphism $f$ of $U$ with $q(f(x)) = t\,q(x)$.
Unconditional. (The count $a(t, U)$ of Lemma 1.3.2 is `Kitaoka.FqCount.lemma132`.) -/
@[kb "kitaoka1993" "§1.3, Lemma 1.3.2, p. 15 (similitude)"]
theorem lemma132_similitude {u : ℕ} (Q : QuadraticForm F (Fin u → F)) (hQ : (polarBilin Q).Nondegenerate)
    (hu : Even u) {t : F} (ht : t ≠ 0) :
    ∃ f : (Fin u → F) ≃ₗ[F] (Fin u → F), ∀ x, Q (f x) = t * Q x := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨k, hc | ⟨W, hW, hQW⟩ | ⟨-, a, -, hQa⟩⟩ := theorem131 F (Fin u → F) Q hQ
  · exact exists_similitude_of_equivalent hc (exists_similitude_hyperbolicSpace k ht)
  · exact exists_similitude_of_equivalent hQW (exists_similitude_prod
      (exists_similitude_hyperbolicSpace k ht)
      (exists_similitude_of_anisotropic (by simp) W hW ht))
  · exfalso
    obtain ⟨e⟩ := hQa
    have := e.toLinearEquiv.finrank_eq
    simp [Module.finrank_prod] at this
    have hk2 : finrank F (Fin k → F × F) = k * 2 := by
      rw [Module.finrank_pi_fintype]
      simp [Module.finrank_prod]
    obtain ⟨r, hr⟩ := hu
    omega

end QuadFormsKB.Kitaoka.Binary
