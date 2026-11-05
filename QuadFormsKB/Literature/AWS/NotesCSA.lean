/-
# Hanke, AWS 2009 notes, §3.1: splitting fields and the norm criterion for division algebras

J. Hanke, *Quadratic Forms and Automorphic Forms*, notes from the 2009 Arizona Winter School,
arXiv:1105.5759 v3 (bibkey `hanke2011aws`; PDF page = printed page), §3.1.

- Thm 3.1.3 (p. 42): a central simple algebra is split by a finite extension; the extension is separable when
  the base field is perfect (in particular in characteristic 0, the notes' main case). Separability over every
  field is proved in `NotesCSASep.lean` (`theorem_3_1_3_separable`).
- Thm 3.1.6 (p. 43): $A$ is a division algebra iff its norm vanishes only at $0$, for the norm computed as a
  determinant after splitting $A$ over an algebraic closure, and for the norm of the regular representation
  (whose determinant is the $n$-th power of the notes' norm, as in the notes' proof).
-/
import QuadFormsKB.Literature.AWS.NotesCh3

open TensorProduct

namespace QuadFormsKB.AWS.Notes

section Norm

variable {F : Type*} [Field F] {A : Type*} [Ring A] [Algebra F A] [FiniteDimensional F A]

/-- In a finite-dimensional algebra $A$ over a field $F$, $\alpha$ is invertible iff the determinant of left
multiplication $L_\alpha : A \to A$ (the norm of the regular representation, `Algebra.norm F α`) is nonzero.
This is the first step of the notes' proof of Thm 3.1.6. -/
theorem isUnit_iff_norm_ne_zero (α : A) : IsUnit α ↔ Algebra.norm F α ≠ 0 := by
  have : IsArtinianRing A := IsArtinianRing.of_finite F A
  rw [Algebra.norm_apply, ← isUnit_iff_ne_zero, ← LinearMap.isUnit_iff_isUnit_det]
  constructor
  · intro h
    exact (Algebra.lmul F A).toRingHom.isUnit_map h
  · intro h
    obtain ⟨β, hβ⟩ := ((Module.End.isUnit_iff _).1 h).2 1
    have hβ' : α * β = 1 := by simpa using hβ
    exact ⟨⟨α, β, hβ', mul_eq_one_comm.1 hβ'⟩, rfl⟩

/-- **Notes, Thm 3.1.6, p. 43 (regular-representation form):** a finite-dimensional nonzero algebra $A$ over
$F$ is a division algebra (every $\alpha \ne 0$ is invertible) iff $N(\alpha) = 0 \Leftrightarrow \alpha = 0$,
where $N(\alpha) = \det(L_\alpha)$ is the norm of the regular representation. For a central simple $A$ of degree
$n$ the notes' proof notes $\det(L_\alpha) = N_{A/k}(\alpha)^n$ with $N_{A/k}$ the notes' (reduced) norm, so the
two norms have the same zeros; see `theorem_3_1_6` for the norm computed through a splitting. -/
@[kb "hanke2011aws" "§3.1, Thm. 3.1.6, p. 43"]
theorem theorem_3_1_6_regular [Nontrivial A] :
    (∀ α : A, α ≠ 0 → IsUnit α) ↔ ∀ α : A, Algebra.norm F α = 0 ↔ α = 0 := by
  constructor
  · intro h α
    refine ⟨fun h0 => ?_, fun h0 => ?_⟩
    · by_contra hα
      exact (isUnit_iff_norm_ne_zero α).1 (h α hα) h0
    · subst h0
      by_contra hn
      exact not_isUnit_zero ((isUnit_iff_norm_ne_zero (0 : A)).2 hn)
  · intro h α hα
    exact (isUnit_iff_norm_ne_zero α).2 fun h0 => hα ((h α).1 h0)

end Norm

section Split

variable (F : Type*) [Field F] (A : Type*) [Ring A] [Algebra F A] [FiniteDimensional F A]

omit [FiniteDimensional F A] in
/-- Left multiplication by $1 \otimes \alpha$ on $L \otimes_F A$ is the base change of left multiplication by
$\alpha$ on $A$. -/
theorem lmul_one_tmul (L : Type*) [Field L] [Algebra F L] (α : A) :
    Algebra.lmul L (L ⊗[F] A) (1 ⊗ₜ α) = (Algebra.lmul F A α).baseChange L := by
  ext x
  simp

/-- $\alpha \in A$ is invertible iff $1 \otimes \alpha$ is invertible in $L \otimes_F A$. -/
theorem isUnit_one_tmul_iff (L : Type*) [Field L] [Algebra F L] (α : A) :
    IsUnit ((1 : L) ⊗ₜ[F] α) ↔ IsUnit α := by
  have : FiniteDimensional L (L ⊗[F] A) := inferInstance
  rw [isUnit_iff_norm_ne_zero (F := L), isUnit_iff_norm_ne_zero (F := F), Algebra.norm_apply,
    Algebra.norm_apply, lmul_one_tmul, LinearMap.det_baseChange]
  simp

/-- **Notes, Thm 3.1.6, p. 43 (norm through a splitting):** let $A$ be a finite-dimensional central simple
algebra over $F$ and $e : \overline F \otimes_F A \cong M_n(\overline F)$ a splitting over an algebraic closure
(one exists: `IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed` with `baseChange_isCentralSimple`). With the
norm $N(\alpha) = \det e(1 \otimes \alpha)$, $A$ is a division algebra (every $\alpha \ne 0$ is invertible) iff
$N(\alpha) = 0 \Leftrightarrow \alpha = 0$.

*Variant:* the notes split over a separable closure $k^{\mathrm{sep}}$ and observe that the norm lies in $k$; here
the splitting is over an algebraic closure and the norm is taken in $\overline F$ (in characteristic $0$ the two
closures agree). -/
@[kb "hanke2011aws" "§3.1, Thm. 3.1.6, p. 43"]
theorem theorem_3_1_6 [Nontrivial A] {n : ℕ}
    (e : AlgebraicClosure F ⊗[F] A ≃ₐ[AlgebraicClosure F] Matrix (Fin n) (Fin n) (AlgebraicClosure F)) :
    (∀ α : A, α ≠ 0 → IsUnit α) ↔ ∀ α : A, (e (1 ⊗ₜ α)).det = 0 ↔ α = 0 := by
  have key : ∀ α : A, IsUnit α ↔ (e (1 ⊗ₜ α)).det ≠ 0 := by
    intro α
    rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det, ← isUnit_one_tmul_iff F A (AlgebraicClosure F)]
    exact (MulEquiv.isUnit_map e.toMulEquiv).symm
  constructor
  · intro h α
    refine ⟨fun h0 => ?_, fun h0 => ?_⟩
    · by_contra hα
      exact (key α).1 (h α hα) h0
    · subst h0
      by_contra hn
      exact not_isUnit_zero ((key 0).2 hn)
  · intro h α hα
    exact (key α).2 fun h0 => hα ((h α).1 h0)

end Split

section Splitting

variable (F : Type*) [Field F] (A : Type*) [Ring A] [Algebra F A] [FiniteDimensional F A]

/-- The intermediate field generated by the matrix entries of $e(1 \otimes b_i)$ for a basis $(b_i)$ of $A$. -/
noncomputable def splitField {n : ℕ}
    (e : AlgebraicClosure F ⊗[F] A ≃ₐ[AlgebraicClosure F] Matrix (Fin n) (Fin n) (AlgebraicClosure F)) :
    IntermediateField F (AlgebraicClosure F) :=
  IntermediateField.adjoin F
    (Set.range fun t : Fin (Module.finrank F A) × Fin n × Fin n =>
      e (1 ⊗ₜ Module.finBasis F A t.1) t.2.1 t.2.2)

/-- The field `splitField F A e` is a finite extension of $F$. -/
theorem finiteDimensional_splitField {n : ℕ}
    (e : AlgebraicClosure F ⊗[F] A ≃ₐ[AlgebraicClosure F] Matrix (Fin n) (Fin n) (AlgebraicClosure F)) :
    FiniteDimensional F (splitField F A e) := by
  unfold splitField
  exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x

/-- Entries of $e(k \otimes a)$, $k \in K$, lie in the field $K$ generated by the entries of the $e(1 \otimes b_i)$. -/
theorem entry_mem_splitField {n : ℕ}
    (e : AlgebraicClosure F ⊗[F] A ≃ₐ[AlgebraicClosure F] Matrix (Fin n) (Fin n) (AlgebraicClosure F))
    (k : splitField F A e) (a : A) (j l : Fin n) :
    e ((k : AlgebraicClosure F) ⊗ₜ a) j l ∈ splitField F A e := by
  have h1 : ∀ a : A, e (1 ⊗ₜ a) j l ∈ splitField F A e := by
    intro a
    have ha := (Module.finBasis F A).sum_repr a
    rw [← ha, tmul_sum, map_sum, Matrix.sum_apply]
    refine (splitField F A e).sum_mem fun i _ => ?_
    rw [tmul_smul, ← algebraMap_smul (AlgebraicClosure F), map_smul, Matrix.smul_apply, smul_eq_mul]
    refine (splitField F A e).mul_mem ((splitField F A e).algebraMap_mem _) (IntermediateField.subset_adjoin F _ ⟨(i, j, l), rfl⟩)
  have : ((k : AlgebraicClosure F) ⊗ₜ[F] a) = (k : AlgebraicClosure F) • ((1 : AlgebraicClosure F) ⊗ₜ a) := by
    rw [smul_tmul', smul_eq_mul, mul_one]
  rw [this, map_smul, Matrix.smul_apply, smul_eq_mul]
  exact (splitField F A e).mul_mem k.2 (h1 a)

/-- **Notes, Thm 3.1.3, p. 42 (finite splitting field):** every finite-dimensional central simple algebra $A$
over a field $F$ is split by a finite extension $K/F$: $K \otimes_F A \cong M_n(K)$ as $K$-algebras. $K$ is taken
inside an algebraic closure $\overline F$, generated by the matrix entries of a splitting over $\overline F$. -/
@[kb "hanke2011aws" "§3.1, Thm. 3.1.3, p. 42"]
theorem theorem_3_1_3_finite [IsSimpleRing A] [Algebra.IsCentral F A] :
    ∃ (K : IntermediateField F (AlgebraicClosure F)) (n : ℕ), FiniteDimensional F K ∧
      Nonempty (K ⊗[F] A ≃ₐ[K] Matrix (Fin n) (Fin n) K) := by
  obtain ⟨hc, hs, hd⟩ := baseChange_isCentralSimple F (AlgebraicClosure F) A
  obtain ⟨n, _, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed (AlgebraicClosure F)
    (AlgebraicClosure F ⊗[F] A)
  set K := splitField F A e
  refine ⟨K, n, finiteDimensional_splitField F A e, ?_⟩
  obtain ⟨_, hsK, hdK⟩ := baseChange_isCentralSimple F K A
  -- `φ : K ⊗ A → M_n(F̄)`, the composite of the inclusion with `e`.
  let ι : K ⊗[F] A →ₐ[K] AlgebraicClosure F ⊗[F] A :=
    Algebra.TensorProduct.map (Algebra.ofId K (AlgebraicClosure F)) (AlgHom.id F A)
  let φ : K ⊗[F] A →ₐ[K] Matrix (Fin n) (Fin n) (AlgebraicClosure F) :=
    (e.toAlgHom.restrictScalars K).comp ι
  let m : Matrix (Fin n) (Fin n) K →ₐ[K] Matrix (Fin n) (Fin n) (AlgebraicClosure F) :=
    (Algebra.ofId K (AlgebraicClosure F)).mapMatrix
  have hm : Function.Injective m := fun x y hxy =>
    Matrix.ext fun j l => (algebraMap K (AlgebraicClosure F)).injective (congrFun (congrFun hxy j) l)
  have hrange : ∀ z, φ z ∈ m.range := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy =>
      obtain ⟨u, hu⟩ := hx
      obtain ⟨v, hv⟩ := hy
      exact ⟨u + v, by rw [map_add, hu, hv, map_add]⟩
    | tmul k a =>
      refine ⟨Matrix.of fun j l => ⟨_, entry_mem_splitField F A e k a j l⟩, ?_⟩
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

/-- **Notes, Thm 3.1.3, p. 42 (finite separable splitting field), perfect base field:** if $F$ is perfect (for
example of characteristic $0$), every finite-dimensional central simple algebra $A$ over $F$ is split by a finite
separable extension $K/F$. For every field, see `theorem_3_1_3_separable` in `NotesCSASep.lean`. -/
@[kb "hanke2011aws" "§3.1, Thm. 3.1.3, p. 42"]
theorem theorem_3_1_3 [IsSimpleRing A] [Algebra.IsCentral F A] [PerfectField F] :
    ∃ (K : IntermediateField F (AlgebraicClosure F)) (n : ℕ), FiniteDimensional F K ∧
      Algebra.IsSeparable F K ∧ Nonempty (K ⊗[F] A ≃ₐ[K] Matrix (Fin n) (Fin n) K) := by
  obtain ⟨K, n, hK, he⟩ := theorem_3_1_3_finite F A
  exact ⟨K, n, hK, Algebra.IsAlgebraic.isSeparable_of_perfectField, he⟩

end Splitting

end QuadFormsKB.AWS.Notes
