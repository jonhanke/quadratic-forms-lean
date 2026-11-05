/-
# Hanke, AWS 2009 notes, Thm 3.1.3 over every field: a finite separable splitting field

J. Hanke, *Quadratic Forms and Automorphic Forms*, notes from the 2009 Arizona Winter School,
arXiv:1105.5759 v3 (bibkey `hanke2011aws`; PDF page = printed page), §3.1, Thm 3.1.3 (p. 42).

`NotesCSA.lean` proves Thm 3.1.3 with separability only over perfect fields. This file removes that restriction.
The notes cite [GS06, Prop 2.2.5] for the proof; we use the following purely algebraic route.

1. (Jacobson's lemma, separably closed case.) A finite-dimensional central division algebra $D$ over a separably
   closed field $K$ is $K$ itself. Every $x \in D$ has $x^{q^m} \in K$ ($q$ the exponential characteristic),
   because the minimal polynomial of $x$ is irreducible and every separable irreducible polynomial over $K$ is
   linear. If $x \notin K$, the inner derivation $\delta = \mathrm{ad}_x$ is nonzero and nilpotent
   ($\delta^{q^m} = \mathrm{ad}_{x^{q^m}} = 0$). Choosing $z$ with $\delta z \ne 0 = \delta^2 z$ and putting
   $s = x z (\delta z)^{-1}$ gives $x s x^{-1} = s + 1$. Then $s^{q^k} = \mu \in K$ and
   $\mu = x s^{q^k} x^{-1} = (s+1)^{q^k} = \mu + 1$, a contradiction.
2. Hence (Wedderburn) every finite-dimensional central simple algebra over a separably closed field is a full
   matrix algebra.
3. Splitting $A$ over the separable closure $F^{\mathrm{sep}}$, the matrix entries of a basis generate a finite
   subextension $K \subseteq F^{\mathrm{sep}}$ that already splits $A$; it is separable over $F$.
-/
import QuadFormsKB.Literature.AWS.NotesCSA

open TensorProduct

namespace QuadFormsKB.AWS.Notes

section Jacobson

variable (K : Type*) [Field K] {D : Type*} [DivisionRing D] [Algebra K D]

/-- Over a separably closed field $K$ with exponential characteristic $q$, every element $x$ of a
finite-dimensional division algebra $D$ has some power $x^{q^m}$ in (the image of) $K$. -/
theorem exists_pow_expChar_eq_algebraMap [IsSepClosed K] [FiniteDimensional K D] (q : ℕ) [hq : ExpChar K q]
    (x : D) : ∃ (m : ℕ) (c : K), x ^ q ^ m = algebraMap K D c := by
  have hint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hirr := minpoly.irreducible hint
  -- a linear polynomial vanishing at `y` puts `y` in `K`
  have lin : ∀ (g : Polynomial K) (y : D), g.degree = 1 → Polynomial.aeval y g = 0 →
      ∃ c : K, y = algebraMap K D c := by
    intro g y hg hy
    have hlc : g.leadingCoeff ≠ 0 := by
      intro h0
      rw [Polynomial.leadingCoeff_eq_zero] at h0
      rw [h0] at hg
      simp at hg
    rw [Polynomial.eq_X_add_C_of_degree_eq_one hg] at hy
    simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X] at hy
    refine ⟨-(g.coeff 0) / g.leadingCoeff, ?_⟩
    have hu : algebraMap K D g.leadingCoeff ≠ 0 := by
      rwa [map_ne_zero]
    have : algebraMap K D g.leadingCoeff * y = algebraMap K D (-(g.coeff 0)) := by
      rw [map_neg, eq_neg_iff_add_eq_zero, hy]
    rw [div_eq_inv_mul, map_mul, ← this, map_inv₀, inv_mul_cancel_left₀ hu]
  cases hq with
  | zero =>
    refine ⟨0, ?_⟩
    simp only [pow_zero, pow_one]
    exact lin _ x (IsSepClosed.degree_eq_one_of_irreducible K hirr hirr.separable) (minpoly.aeval K x)
  | prime hp =>
    obtain ⟨m, g, hgs, hg⟩ := Polynomial.exists_separable_of_irreducible q hirr hp.ne_zero
    have hgirr : Irreducible g :=
      Polynomial.of_irreducible_expand_pow hp.ne_zero (hg ▸ hirr)
    refine ⟨m, lin g _ (IsSepClosed.degree_eq_one_of_irreducible K hgirr hgs) ?_⟩
    rw [← Polynomial.expand_aeval, hg, minpoly.aeval]

/-- **Jacobson's lemma over a separably closed field:** a finite-dimensional central division algebra $D$ over a
separably closed field $K$ is $K$: every element of $D$ is the image of an element of $K$. -/
theorem mem_range_algebraMap_of_isSepClosed [IsSepClosed K] [FiniteDimensional K D] [Algebra.IsCentral K D]
    (x : D) : ∃ c : K, x = algebraMap K D c := by
  obtain ⟨q, hq⟩ := ExpChar.exists K
  have hqD : ExpChar D q := expChar_of_injective_algebraMap (algebraMap K D).injective q
  by_contra hx
  -- `x` is not central
  have hxc : x ∉ Subalgebra.center K D := fun h => hx ((Algebra.IsCentral.mem_center_iff K).1 h)
  rw [Subalgebra.mem_center_iff] at hxc
  push Not at hxc
  obtain ⟨y₀, hy₀⟩ := hxc
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hy₀
  -- the inner derivation `δ = ad x` in `End_K(D)`
  let δ : Module.End K D := LinearMap.mulLeft K x - LinearMap.mulRight K x
  have hδ : ∀ y, δ y = x * y - y * x := fun y => rfl
  have hcomm : Commute (LinearMap.mulLeft K x) (LinearMap.mulRight K x) :=
    LinearMap.commute_mulLeft_right x x
  have hqE : ExpChar (Module.End K D) q :=
    expChar_of_injective_algebraMap (algebraMap K (Module.End K D)).injective q
  obtain ⟨m, c, hc⟩ := exists_pow_expChar_eq_algebraMap K q x
  have hnil : ∃ k, δ ^ k = 0 := by
    refine ⟨q ^ m, ?_⟩
    rw [sub_pow_expChar_pow_of_commute _ _ hcomm, LinearMap.pow_mulLeft, LinearMap.pow_mulRight, hc]
    ext y
    simp [Algebra.commutes]
  classical
  let k₀ := Nat.find hnil
  have hk₀ : δ ^ k₀ = 0 := Nat.find_spec hnil
  have hk₀1 : 2 ≤ k₀ := by
    by_contra hlt
    interval_cases h : k₀
    · rw [pow_zero] at hk₀
      exact one_ne_zero hk₀
    · rw [pow_one] at hk₀
      apply hy₀
      have := LinearMap.congr_fun hk₀ y₀
      rw [hδ, LinearMap.zero_apply, sub_eq_zero] at this
      exact this.symm
  have hlt : δ ^ (k₀ - 1) ≠ 0 := Nat.find_min hnil (by omega)
  obtain ⟨y, hy⟩ : ∃ y, (δ ^ (k₀ - 1)) y ≠ 0 := by
    by_contra h
    push Not at h
    exact hlt (LinearMap.ext h)
  set z := (δ ^ (k₀ - 2)) y
  have hz1 : δ z ≠ 0 := by
    rw [← Module.End.mul_apply, ← pow_succ']
    rwa [show k₀ - 2 + 1 = k₀ - 1 by omega]
  have hz2 : δ (δ z) = 0 := by
    have e : δ (δ z) = (δ ^ (k₀ - 2 + 1 + 1)) y := by
      rw [pow_succ', pow_succ']
      rfl
    rw [e, show k₀ - 2 + 1 + 1 = k₀ by omega, hk₀, LinearMap.zero_apply]
  set w := δ z
  have hw : x * w = w * x := by
    have := hz2
    rw [hδ, sub_eq_zero] at this
    exact this
  -- `t = z w⁻¹` satisfies `x t - t x = 1`, and `s = x t` satisfies `x s = (s + 1) x`
  have hwinv : x * w⁻¹ = w⁻¹ * x := ((Commute.inv_right₀ (hw : Commute x w))).eq
  have ht : x * (z * w⁻¹) - z * w⁻¹ * x = 1 := by
    have : x * (z * w⁻¹) - z * w⁻¹ * x = (x * z - z * x) * w⁻¹ := by
      rw [sub_mul, mul_assoc z, ← hwinv, ← mul_assoc, ← mul_assoc]
    rw [this, ← hδ, mul_inv_cancel₀ hz1]
  obtain ⟨s, hsdef⟩ : ∃ s, s = x * (z * w⁻¹) := ⟨_, rfl⟩
  have hs : SemiconjBy x s (s + 1) := by
    unfold SemiconjBy
    have : x * s - s * x = x := by
      rw [hsdef, mul_assoc x _ x, ← mul_sub, ht, mul_one]
    rw [add_mul, one_mul, add_comm]
    exact sub_eq_iff_eq_add.1 this
  obtain ⟨m', μ, hμ⟩ := exists_pow_expChar_eq_algebraMap K q s
  have h1 := hs.pow_right (q ^ m')
  rw [add_pow_expChar_pow_of_commute _ _ (Commute.one_right s), one_pow, hμ] at h1
  unfold SemiconjBy at h1
  rw [← Algebra.commutes μ x, add_mul, one_mul] at h1
  exact hx0 (by simpa using h1)

/-- **Wedderburn's theorem over a separably closed field:** a finite-dimensional central simple algebra $R$ over
a separably closed field $L$ is isomorphic to a full matrix algebra $M_n(L)$, $n \ge 1$. -/
theorem exists_algEquiv_matrix_of_isSepClosed (L R : Type*) [Field L] [IsSepClosed L] [Ring R] [Algebra L R]
    [IsSimpleRing R] [Algebra.IsCentral L R] [FiniteDimensional L R] :
    ∃ (n : ℕ) (_ : NeZero n), Nonempty (R ≃ₐ[L] Matrix (Fin n) (Fin n) L) := by
  have := IsArtinianRing.of_finite L R
  obtain ⟨n, hn, D, _, _, _, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite L R
  have hcM : Algebra.IsCentral L (Matrix (Fin n) (Fin n) D) := Algebra.IsCentral.of_algEquiv L R _ e
  have hcD : Algebra.IsCentral L D := by
    refine ⟨fun d hd => ?_⟩
    have hmem : Matrix.scalarAlgHom (Fin n) L d ∈ Subalgebra.center L (Matrix (Fin n) (Fin n) D) := by
      rw [Matrix.subalgebraCenter_eq_scalarAlgHom_map]
      exact ⟨d, hd, rfl⟩
    obtain ⟨l, hl⟩ := (Algebra.IsCentral.mem_center_iff L).1 hmem
    refine ⟨l, ?_⟩
    have := congrFun (congrFun hl 0) 0
    simpa [Matrix.algebraMap_eq_diagonal] using this.symm
  have hbij : Function.Bijective (algebraMap L D) :=
    ⟨(algebraMap L D).injective, fun d => by
      obtain ⟨c, hc⟩ := mem_range_algebraMap_of_isSepClosed L d
      exact ⟨c, hc.symm⟩⟩
  exact ⟨n, hn, ⟨e.trans <| .mapMatrix <| .symm <| .ofBijective (Algebra.ofId L D) hbij⟩⟩

end Jacobson

section Splitting

variable (F : Type*) [Field F] (A : Type*) [Ring A] [Algebra F A] [FiniteDimensional F A]
  (Ω : Type*) [Field Ω] [Algebra F Ω]

/-- The intermediate field generated by the matrix entries of $e(1 \otimes b_i)$ for a basis $(b_i)$ of $A$. -/
noncomputable def splitFieldIn {n : ℕ}
    (e : Ω ⊗[F] A ≃ₐ[Ω] Matrix (Fin n) (Fin n) (Ω)) :
    IntermediateField F (Ω) :=
  IntermediateField.adjoin F
    (Set.range fun t : Fin (Module.finrank F A) × Fin n × Fin n =>
      e (1 ⊗ₜ Module.finBasis F A t.1) t.2.1 t.2.2)

/-- The field `splitFieldIn F A Ω e` is a finite extension of $F$. -/
theorem finiteDimensional_splitFieldIn [Algebra.IsSeparable F Ω] {n : ℕ}
    (e : Ω ⊗[F] A ≃ₐ[Ω] Matrix (Fin n) (Fin n) (Ω)) :
    FiniteDimensional F (splitFieldIn F A Ω e) := by
  unfold splitFieldIn
  exact IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsSeparable.isSeparable F x).isIntegral

/-- Entries of $e(k \otimes a)$, $k \in K$, lie in the field $K$ generated by the entries of the $e(1 \otimes b_i)$. -/
theorem entry_mem_splitFieldIn {n : ℕ}
    (e : Ω ⊗[F] A ≃ₐ[Ω] Matrix (Fin n) (Fin n) (Ω))
    (k : splitFieldIn F A Ω e) (a : A) (j l : Fin n) :
    e ((k : Ω) ⊗ₜ a) j l ∈ splitFieldIn F A Ω e := by
  have h1 : ∀ a : A, e (1 ⊗ₜ a) j l ∈ splitFieldIn F A Ω e := by
    intro a
    have ha := (Module.finBasis F A).sum_repr a
    rw [← ha, tmul_sum, map_sum, Matrix.sum_apply]
    refine (splitFieldIn F A Ω e).sum_mem fun i _ => ?_
    rw [tmul_smul, ← algebraMap_smul (Ω), map_smul, Matrix.smul_apply, smul_eq_mul]
    refine (splitFieldIn F A Ω e).mul_mem ((splitFieldIn F A Ω e).algebraMap_mem _) (IntermediateField.subset_adjoin F _ ⟨(i, j, l), rfl⟩)
  have : ((k : Ω) ⊗ₜ[F] a) = (k : Ω) • ((1 : Ω) ⊗ₜ a) := by
    rw [smul_tmul', smul_eq_mul, mul_one]
  rw [this, map_smul, Matrix.smul_apply, smul_eq_mul]
  exact (splitFieldIn F A Ω e).mul_mem k.2 (h1 a)

/-- Splitting inside a separably closed separable extension $\Omega/F$: a finite-dimensional central simple
algebra $A$ over $F$ is split by a finite separable subextension $K$ of $\Omega/F$. -/
theorem exists_finite_separable_splitting [IsSepClosed Ω] [Algebra.IsSeparable F Ω] [IsSimpleRing A]
    [Algebra.IsCentral F A] :
    ∃ (K : IntermediateField F Ω) (n : ℕ), FiniteDimensional F K ∧
      Algebra.IsSeparable F K ∧ Nonempty (K ⊗[F] A ≃ₐ[K] Matrix (Fin n) (Fin n) K) := by
  obtain ⟨hc, hs, hd⟩ := baseChange_isCentralSimple F (Ω) A
  obtain ⟨n, _, ⟨e⟩⟩ := exists_algEquiv_matrix_of_isSepClosed (Ω)
    (Ω ⊗[F] A)
  set K := splitFieldIn F A (Ω) e
  refine ⟨K, n, finiteDimensional_splitFieldIn F A (Ω) e,
    Algebra.isSeparable_tower_bot_of_isSeparable F K Ω, ?_⟩
  obtain ⟨_, hsK, hdK⟩ := baseChange_isCentralSimple F K A
  -- `φ : K ⊗ A → M_n(F̄)`, the composite of the inclusion with `e`.
  let ι : K ⊗[F] A →ₐ[K] Ω ⊗[F] A :=
    Algebra.TensorProduct.map (Algebra.ofId K (Ω)) (AlgHom.id F A)
  let φ : K ⊗[F] A →ₐ[K] Matrix (Fin n) (Fin n) (Ω) :=
    (e.toAlgHom.restrictScalars K).comp ι
  let m : Matrix (Fin n) (Fin n) K →ₐ[K] Matrix (Fin n) (Fin n) (Ω) :=
    (Algebra.ofId K (Ω)).mapMatrix
  have hm : Function.Injective m := fun x y hxy =>
    Matrix.ext fun j l => (algebraMap K (Ω)).injective (congrFun (congrFun hxy j) l)
  have hrange : ∀ z, φ z ∈ m.range := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy =>
      obtain ⟨u, hu⟩ := hx
      obtain ⟨v, hv⟩ := hy
      exact ⟨u + v, by rw [map_add, hu, hv, map_add]⟩
    | tmul k a =>
      refine ⟨Matrix.of fun j l => ⟨_, entry_mem_splitFieldIn F A (Ω) e k a j l⟩, ?_⟩
      ext j l
      rfl
  let ψ : K ⊗[F] A →ₐ[K] Matrix (Fin n) (Fin n) K :=
    ((AlgEquiv.ofInjective m hm).symm.toAlgHom).comp (φ.codRestrict m.range hrange)
  have hinj : Function.Injective ψ := ψ.toRingHom.injective
  have hdim : Module.finrank K (K ⊗[F] A) = Module.finrank K (Matrix (Fin n) (Fin n) K) := by
    rw [hdK, ← hd, e.toLinearEquiv.finrank_eq, Module.finrank_matrix, Module.finrank_matrix]
    simp
  have hsurj : Function.Surjective ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := ψ.toLinearMap)).1 hinj
  exact ⟨AlgEquiv.ofBijective ψ ⟨hinj, hsurj⟩⟩


/-- **Notes, Thm 3.1.3, p. 42 (finite separable splitting field), every field:** every finite-dimensional central
simple algebra $A$ over a field $F$ is split by a finite separable extension $K/F$:
$K \otimes_F A \cong M_n(K)$ as $K$-algebras. $K$ is taken inside a separable closure $F^{\mathrm{sep}}$ (Mathlib's
`SeparableClosure F`), generated by the matrix entries of a splitting over $F^{\mathrm{sep}}$. This removes the
perfectness hypothesis of `theorem_3_1_3`. The notes cite [GS06, Prop 2.2.5]; the proof here goes through Jacobson's
lemma (`mem_range_algebraMap_of_isSepClosed`). -/
@[kb "hanke2011aws" "§3.1, Thm. 3.1.3, p. 42"]
theorem theorem_3_1_3_separable [IsSimpleRing A] [Algebra.IsCentral F A] :
    ∃ (K : IntermediateField F (SeparableClosure F)) (n : ℕ), FiniteDimensional F K ∧
      Algebra.IsSeparable F K ∧ Nonempty (K ⊗[F] A ≃ₐ[K] Matrix (Fin n) (Fin n) K) := by
  exact exists_finite_separable_splitting F A (SeparableClosure F)

end Splitting


end QuadFormsKB.AWS.Notes
