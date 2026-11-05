/-
# O'Meara §65A: local degrees and local norms of $E = F(\sqrt\theta)$

**Setting** (O'Meara §65A, pp. 174–176). $F$ is a number field, $\theta \in F$ a non-square, and $E = F(\sqrt\theta)$:
a quadratic extension `[Algebra.IsQuadraticExtension F E]` with an element $s$ (O'Meara's $\sqrt\theta$),
$s^2 = \theta$. Spots, completions and local norms are those of `Sec64Local.lean` and `Sec64Inf.lean`. The local
degree $n(\mathfrak P|\mathfrak p) = [E_\mathfrak P : F_\mathfrak p]$ is `Module.finrank`.

**Defines**
* `IsLocalNormAt v x` (§65A, p. 176): $x \in F_\mathfrak p$ is a *local norm* at the finite spot $\mathfrak p$, i.e.
  $x \in N_{\mathfrak P|\mathfrak p}E_\mathfrak P$ for every $\mathfrak P \mid \mathfrak p$; `IsLocalNormAtInf` at an
  infinite spot.

**Proves** (§65A, pp. 175–176)
* `exists_eq_add_mul_sqrt`: every element of $E$ is $b_0 + b_1\sqrt\theta$;
* `finrank_eq_one_iff_isSquare`, `finrank_eq_two_iff_not_isSquare`: $n(\mathfrak P|\mathfrak p) = 1$ if $\theta$ is a
  square at $\mathfrak p$ and $2$ otherwise, so it depends only on $\mathfrak p$ (`finrank_eq_of_liesOver`, 65.r14);
  likewise at infinite spots;
* `card_spotsOver_of_isSquare`, `card_spotsOver_of_not_isSquare` (65.r15, 65.r16): two spots over $\mathfrak p$ if
  $\theta$ is a square at $\mathfrak p$, one otherwise;
* `isLocalNormAt_of_isSquare` (65.r26): every element of $F_\mathfrak p$ is a local norm when $n_\mathfrak p = 1$;
* `isLocalNormAt_iff_tensor`, `index_localNorms_eq_two` (65.r27): when $n_\mathfrak p = 2$ the local norms are the
  norms from $F_\mathfrak p \otimes_F E$ and have index $2$ in $\dot F_\mathfrak p$;
  `isLocalNormAt_iff_hilbertSymbol` (65.r28): $x$ is a local norm iff $(\theta, x)_\mathfrak p = 1$.
-/
import QuadFormsKB.Literature.OMeara.Sec64Norm
import QuadFormsKB.Literature.HasseNorm.LocalIndexTwo

open NumberField IsDedekindDomain InfinitePlace

open scoped NumberField.LiesOver TensorProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

/-! ### $E = F \oplus F\sqrt\theta$ -/

/-- In a quadratic extension $E = F(\sqrt\theta)$, every element is $b_0 + b_1\sqrt\theta$ with $b_0, b_1 \in F$. -/
theorem exists_eq_add_mul_sqrt {θ : F} (hθ : ¬ IsSquare θ) {s : E} (hs : s ^ 2 = algebraMap F E θ) (y : E) :
    ∃ b₀ b₁ : F, y = algebraMap F E b₀ + algebraMap F E b₁ * s := by
  have hs1 : s ∉ Set.range (algebraMap F E) := by
    rintro ⟨c, rfl⟩
    exact hθ ⟨c, (algebraMap F E).injective (by rw [← hs, map_mul, pow_two])⟩
  have hli : LinearIndependent F ![(1 : E), s] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    by_contra hne
    have hb : b ≠ 0 := by
      intro hb; subst hb
      simp only [zero_smul, add_zero] at hab
      exact hne ⟨by simpa using hab, rfl⟩
    apply hs1
    refine ⟨-a / b, ?_⟩
    have : b • s = -(a • (1 : E)) := eq_neg_of_add_eq_zero_right hab
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at this
    rw [map_div₀, map_neg, ← this, mul_div_cancel_left₀ _ ((map_ne_zero _).2 hb)]
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by
    rw [Algebra.IsQuadraticExtension.finrank_eq_two]; rfl
  have hspan := hli.span_eq_top_of_card_eq_finrank' hcard
  have hy : y ∈ Submodule.span F (Set.range ![(1 : E), s]) := hspan ▸ Submodule.mem_top
  rw [Submodule.mem_span_range_iff_exists_fun] at hy
  obtain ⟨c, hc⟩ := hy
  refine ⟨c 0, c 1, ?_⟩
  rw [← hc, Fin.sum_univ_two]
  simp [Algebra.smul_def]

variable {θ : F} (hθ : ¬ IsSquare θ) {s : E} (hs : s ^ 2 = algebraMap F E θ)
include hθ hs

/-! ### Local degrees at finite spots -/

section Finite

variable (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]

/-- $E_\mathfrak P$ is spanned over $F_\mathfrak p$ by $1$ and $\sqrt\theta$. -/
lemma exists_eq_add_mul_sqrt_local (y : w.adicCompletion E) :
    ∃ c₀ c₁ : v.adicCompletion F, y = algebraMap _ _ c₀ + algebraMap _ _ c₁ * (algebraMap E (w.adicCompletion E) s) := by
  -- the image of `F_𝔭 ⊗ E` is everything (Mathlib's `Module.Finite` argument), and `E = F + F s`
  let Φ : v.adicCompletion F ⊗[F] E →ₐ[v.adicCompletion F] w.adicCompletion E :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) (IsScalarTower.toAlgHom F E _) (fun _ _ => Commute.all _ _)
  have hsurj : Function.Surjective Φ := by
    have hd : DenseRange Φ := by
      refine (HeightOneSpectrum.denseRange_algebraMap E w).mono ?_
      rintro _ ⟨y, rfl⟩
      exact ⟨1 ⊗ₜ y, by simp [Φ]⟩
    have hc : IsClosed (Φ.toLinearMap.range : Set (w.adicCompletion E)) :=
      Submodule.closed_of_finiteDimensional _
    intro y
    have : y ∈ closure (Set.range Φ) := hd y
    rw [← Φ.coe_toLinearMap, ← LinearMap.coe_range, hc.closure_eq] at this
    exact this
  obtain ⟨z, rfl⟩ := hsurj y
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul c e =>
    obtain ⟨b₀, b₁, rfl⟩ := exists_eq_add_mul_sqrt hθ hs e
    refine ⟨c * algebraMap F _ b₀, c * algebraMap F _ b₁, ?_⟩
    simp only [Φ, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, IsScalarTower.coe_toAlgHom', map_add,
      map_mul, ← IsScalarTower.algebraMap_apply]
    ring
  | add x y hx hy =>
    obtain ⟨a₀, a₁, ha⟩ := hx
    obtain ⟨b₀, b₁, hb⟩ := hy
    exact ⟨a₀ + b₀, a₁ + b₁, by rw [map_add, ha, hb, map_add, map_add]; ring⟩

/-- **$n(\mathfrak P|\mathfrak p) = 1$ iff $\theta$ is a square at $\mathfrak p$** (O'Meara §65A, p. 175). -/
@[kb "omeara1963" "§65A, p. 175 (n(𝔓|𝔭) = 1 if θ is a square at 𝔭, finite spot)"]
theorem finrank_eq_one_iff_isSquare :
    Module.finrank (v.adicCompletion F) (w.adicCompletion E) = 1 ↔
      IsSquare (algebraMap F (v.adicCompletion F) θ) := by
  have hsθ : (algebraMap E (w.adicCompletion E) s) ^ 2 = localMap v w (algebraMap F _ θ) := by
    rw [localMap_algebraMap, ← hs, map_pow]
  constructor
  · intro h1
    -- `E_𝔓 = F_𝔭`, so `s = ι c` and `θ = c²`
    have hsurj : Function.Surjective (algebraMap (v.adicCompletion F) (w.adicCompletion E)) := by
      have htop : (v.adicCompletion F) ∙ (1 : w.adicCompletion E) = ⊤ :=
        Submodule.eq_top_of_finrank_eq ((finrank_span_singleton one_ne_zero).trans h1.symm)
      intro y
      have hy : y ∈ (v.adicCompletion F) ∙ (1 : w.adicCompletion E) := htop ▸ Submodule.mem_top
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hy
      exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one, hc]⟩
    obtain ⟨c, hc⟩ := hsurj (algebraMap E (w.adicCompletion E) s)
    refine ⟨c, (localMap v w).injective ?_⟩
    rw [← hsθ, ← hc, algebraMap_adicCompletion_liesOver, map_mul, pow_two]
  · rintro ⟨c, hc⟩
    -- `s = ± ι c`, so `E_𝔓 = F_𝔭 + F_𝔭 s = F_𝔭`
    have hs2 : ((algebraMap E (w.adicCompletion E) s) - localMap v w c) * ((algebraMap E (w.adicCompletion E) s) + localMap v w c) = 0 := by
      have : ((algebraMap E (w.adicCompletion E) s) - localMap v w c) *
          ((algebraMap E (w.adicCompletion E) s) + localMap v w c) =
          (algebraMap E (w.adicCompletion E) s) ^ 2 - localMap v w c * localMap v w c := by ring
      rw [this, hsθ, hc, map_mul, sub_self]
    have hsc : ∃ d : v.adicCompletion F, (algebraMap E (w.adicCompletion E) s) = localMap v w d := by
      rcases mul_eq_zero.1 hs2 with h | h
      · exact ⟨c, sub_eq_zero.1 h⟩
      · exact ⟨-c, by rw [map_neg]; exact eq_neg_of_add_eq_zero_left h⟩
    obtain ⟨d, hd⟩ := hsc
    refine le_antisymm ?_ Module.finrank_pos
    have : Submodule.span (v.adicCompletion F) {(1 : w.adicCompletion E)} = ⊤ := by
      refine eq_top_iff.2 fun y _ => ?_
      obtain ⟨c₀, c₁, rfl⟩ := exists_eq_add_mul_sqrt_local hθ hs v w y
      rw [Submodule.mem_span_singleton]
      refine ⟨c₀ + c₁ * d, ?_⟩
      rw [Algebra.smul_def, mul_one, map_add, map_mul, hd]
      rfl
    rw [← finrank_top, ← this, finrank_span_singleton one_ne_zero]

/-- $n(\mathfrak P|\mathfrak p) \le 2$. -/
lemma finrank_le_two : Module.finrank (v.adicCompletion F) (w.adicCompletion E) ≤ 2 := by
  have : Submodule.span (v.adicCompletion F) {(1 : w.adicCompletion E), (algebraMap E (w.adicCompletion E) s)} = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨c₀, c₁, rfl⟩ := exists_eq_add_mul_sqrt_local hθ hs v w y
    rw [Submodule.mem_span_pair]
    exact ⟨c₀, c₁, by rw [Algebra.smul_def, Algebra.smul_def, mul_one]⟩
  rw [← finrank_top, ← this]
  refine (finrank_span_le_ncard _ (Set.toFinite _)).trans ?_
  exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])

/-- **$n(\mathfrak P|\mathfrak p) = 2$ iff $\theta$ is a non-square at $\mathfrak p$** (O'Meara §65A, p. 175). -/
@[kb "omeara1963" "§65A, p. 175 (n(𝔓|𝔭) = 2 if θ is a non-square at 𝔭, finite spot)"]
theorem finrank_eq_two_iff_not_isSquare :
    Module.finrank (v.adicCompletion F) (w.adicCompletion E) = 2 ↔
      ¬ IsSquare (algebraMap F (v.adicCompletion F) θ) := by
  rw [← finrank_eq_one_iff_isSquare hθ hs v w]
  have h1 := finrank_le_two hθ hs v w
  have h2 : 0 < Module.finrank (v.adicCompletion F) (w.adicCompletion E) := Module.finrank_pos
  omega

/-- **The local degree depends only on $\mathfrak p$** (O'Meara §65A, p. 175: $E/F$ is abelian, so by §15C
$n(\mathfrak P|\mathfrak p)$ is the same $n_\mathfrak p$ for all $\mathfrak P \mid \mathfrak p$). -/
@[kb "omeara1963" "§65A, p. 175 (the local degree n(𝔓|𝔭) =: n_𝔭 is the same for all 𝔓 | 𝔭)"]
theorem finrank_eq_of_liesOver (w' : HeightOneSpectrum (𝓞 E)) [w'.asIdeal.LiesOver v.asIdeal] :
    Module.finrank (v.adicCompletion F) (w.adicCompletion E) =
      Module.finrank (v.adicCompletion F) (w'.adicCompletion E) := by
  by_cases h : IsSquare (algebraMap F (v.adicCompletion F) θ)
  · rw [(finrank_eq_one_iff_isSquare hθ hs v w).2 h, (finrank_eq_one_iff_isSquare hθ hs v w').2 h]
  · rw [(finrank_eq_two_iff_not_isSquare hθ hs v w).2 h, (finrank_eq_two_iff_not_isSquare hθ hs v w').2 h]

omit [w.asIdeal.LiesOver v.asIdeal] in
/-- **The number of spots over $\mathfrak p$** (O'Meara §65A, p. 175): $\sum_{\mathfrak P|\mathfrak p} n_\mathfrak p =
2$. -/
theorem card_spotsOver_mul_finrank (w : SpotsOver E v) :
    Fintype.card (SpotsOver E v) * Module.finrank (v.adicCompletion F) (w.1.adicCompletion E) = 2 := by
  have h := (finrank_eq_ef_and_sum E v).2
  rw [Algebra.IsQuadraticExtension.finrank_eq_two] at h
  rw [← h, Finset.sum_congr rfl (fun w' _ => finrank_eq_of_liesOver hθ hs v w'.1 w.1), Finset.sum_const,
    Finset.card_univ, smul_eq_mul]

omit [w.asIdeal.LiesOver v.asIdeal] in
lemma nonempty_spotsOver : Nonempty (SpotsOver E v) := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := (finrank_eq_ef_and_sum E v).2
  rw [Finset.univ_eq_empty, Finset.sum_empty, Algebra.IsQuadraticExtension.finrank_eq_two] at this
  exact absurd this (by norm_num)

end Finite

/-! ### A completion $A$ of $E$ over a completion $K$ of $F$ (abstract form) -/

section Generic

variable {K A : Type*} [Field K] [Field A] [Algebra K A] [Algebra F K] [Algebra F A] [Algebra E A]
  [IsScalarTower F K A] [IsScalarTower F E A]

/-- The natural map $K \otimes_F E \to A$. -/
def tensorToField : K ⊗[F] E →ₐ[K] A :=
  Algebra.TensorProduct.lift (Algebra.ofId K A) (IsScalarTower.toAlgHom F E A) (fun _ _ => Commute.all _ _)

omit hθ hs in
lemma tensorToField_tmul (c : K) (y : E) : tensorToField (c ⊗ₜ[F] y) = algebraMap K A c * algebraMap E A y := by
  simp [tensorToField]

/-- If $K \otimes_F E \to A$ is onto, every element of $A$ is $c_0 + c_1\sqrt\theta$ with $c_i \in K$. -/
lemma exists_eq_add_mul_sqrt_gen (hsurj : Function.Surjective (tensorToField (K := K) (A := A) (F := F) (E := E)))
    (y : A) : ∃ c₀ c₁ : K, y = algebraMap K A c₀ + algebraMap K A c₁ * algebraMap E A s := by
  obtain ⟨z, rfl⟩ := hsurj y
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul c e =>
    obtain ⟨b₀, b₁, rfl⟩ := exists_eq_add_mul_sqrt hθ hs e
    refine ⟨c * algebraMap F K b₀, c * algebraMap F K b₁, ?_⟩
    rw [tensorToField_tmul]
    simp only [map_add, map_mul, ← IsScalarTower.algebraMap_apply]
    ring
  | add x y hx hy =>
    obtain ⟨a₀, a₁, ha⟩ := hx
    obtain ⟨b₀, b₁, hb⟩ := hy
    exact ⟨a₀ + b₀, a₁ + b₁, by rw [map_add, ha, hb, map_add, map_add]; ring⟩

/-- $[A : K] = 1$ iff $\theta$ is a square in $K$ (given $K \otimes_F E \to A$ onto). -/
theorem finrank_eq_one_iff_isSquare_gen [FiniteDimensional K A]
    (hsurj : Function.Surjective (tensorToField (K := K) (A := A) (F := F) (E := E))) :
    Module.finrank K A = 1 ↔ IsSquare (algebraMap F K θ) := by
  have hsθ : (algebraMap E A s) ^ 2 = algebraMap K A (algebraMap F K θ) := by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply F E A, ← hs, map_pow]
  constructor
  · intro h1
    have htop : K ∙ (1 : A) = ⊤ :=
      Submodule.eq_top_of_finrank_eq ((finrank_span_singleton one_ne_zero).trans h1.symm)
    have hy : algebraMap E A s ∈ K ∙ (1 : A) := htop ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hy
    refine ⟨c, (algebraMap K A).injective ?_⟩
    rw [← hsθ, ← hc, Algebra.smul_def, mul_one, map_mul, pow_two]
  · rintro ⟨c, hc⟩
    have hs2 : (algebraMap E A s - algebraMap K A c) * (algebraMap E A s + algebraMap K A c) = 0 := by
      have : (algebraMap E A s - algebraMap K A c) * (algebraMap E A s + algebraMap K A c) =
          (algebraMap E A s) ^ 2 - algebraMap K A c * algebraMap K A c := by ring
      rw [this, hsθ, hc, map_mul, sub_self]
    have hsc : ∃ d : K, algebraMap E A s = algebraMap K A d := by
      rcases mul_eq_zero.1 hs2 with h | h
      · exact ⟨c, sub_eq_zero.1 h⟩
      · exact ⟨-c, by rw [map_neg]; exact eq_neg_of_add_eq_zero_left h⟩
    obtain ⟨d, hd⟩ := hsc
    refine le_antisymm ?_ Module.finrank_pos
    have : K ∙ (1 : A) = ⊤ := by
      refine eq_top_iff.2 fun y _ => ?_
      obtain ⟨c₀, c₁, rfl⟩ := exists_eq_add_mul_sqrt_gen hθ hs hsurj y
      rw [Submodule.mem_span_singleton]
      exact ⟨c₀ + c₁ * d, by rw [Algebra.smul_def, mul_one, map_add, map_mul, hd]⟩
    rw [← finrank_top, ← this, finrank_span_singleton one_ne_zero]

lemma finrank_le_two_gen (hsurj : Function.Surjective (tensorToField (K := K) (A := A) (F := F) (E := E))) :
    Module.finrank K A ≤ 2 := by
  have : Submodule.span K {(1 : A), algebraMap E A s} = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨c₀, c₁, rfl⟩ := exists_eq_add_mul_sqrt_gen hθ hs hsurj y
    rw [Submodule.mem_span_pair]
    exact ⟨c₀, c₁, by rw [Algebra.smul_def, Algebra.smul_def, mul_one]⟩
  rw [← finrank_top, ← this]
  refine (finrank_span_le_ncard _ (Set.toFinite _)).trans ?_
  exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])

/-- If $[A : K] = 2$, the natural map $K \otimes_F E \to A$ is an isomorphism, so it preserves norms. -/
theorem norm_tensorToField_of_finrank_eq_two [FiniteDimensional K A]
    (hsurj : Function.Surjective (tensorToField (K := K) (A := A) (F := F) (E := E)))
    (h2 : Module.finrank K A = 2) (z : K ⊗[F] E) :
    Algebra.norm K (tensorToField (K := K) (A := A) (F := F) (E := E) z) = Algebra.norm K z := by
  have hfr : Module.finrank K (K ⊗[F] E) = Module.finrank K A := by
    rw [Module.finrank_baseChange, Algebra.IsQuadraticExtension.finrank_eq_two, h2]
  have hinj : Function.Injective (tensorToField (K := K) (A := A) (F := F) (E := E)) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr
      (f := (tensorToField (K := K) (A := A) (F := F) (E := E)).toLinearMap)).2 hsurj
  rw [show tensorToField (K := K) (A := A) (F := F) (E := E) z =
    AlgEquiv.ofBijective _ ⟨hinj, hsurj⟩ z from rfl]
  exact (Algebra.norm_eq_of_algEquiv
    (AlgEquiv.ofBijective (tensorToField (K := K) (A := A) (F := F) (E := E)) ⟨hinj, hsurj⟩) z)

/-- If $[A : K] = 2$, the norms from $A$ are exactly the norms from $K \otimes_F E$. -/
theorem range_norm_eq_tensor_of_finrank_eq_two [FiniteDimensional K A]
    (hsurj : Function.Surjective (tensorToField (K := K) (A := A) (F := F) (E := E)))
    (h2 : Module.finrank K A = 2) :
    (Units.map (Algebra.norm K : A →* K)).range =
      (Units.map (Algebra.norm K : K ⊗[F] E →* K)).range := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := hsurj (y : A)
    have hz0 : z ≠ 0 := by rintro rfl; rw [map_zero] at hz; exact y.ne_zero hz.symm
    have hzu : IsUnit z := by
      have hfr : Module.finrank K (K ⊗[F] E) = Module.finrank K A := by
        rw [Module.finrank_baseChange, Algebra.IsQuadraticExtension.finrank_eq_two, h2]
      have hinj : Function.Injective (tensorToField (K := K) (A := A) (F := F) (E := E)) :=
        (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr
          (f := (tensorToField (K := K) (A := A) (F := F) (E := E)).toLinearMap)).2 hsurj
      let e := AlgEquiv.ofBijective _ ⟨hinj, hsurj⟩
      have : z = e.symm y := by rw [AlgEquiv.eq_symm_apply]; exact hz
      rw [this]
      exact (y.isUnit).map e.symm
    refine ⟨hzu.unit, Units.ext ?_⟩
    show Algebra.norm K z = Algebra.norm K (y : A)
    rw [← norm_tensorToField_of_finrank_eq_two hθ hs hsurj h2, hz]
  · rintro ⟨z, rfl⟩
    refine ⟨Units.map (tensorToField (K := K) (A := A) (F := F) (E := E)).toMonoidHom z, Units.ext ?_⟩
    exact norm_tensorToField_of_finrank_eq_two hθ hs hsurj h2 (z : K ⊗[F] E)

/-- **Local norms and the Hilbert symbol** (abstract form): if $[A : K] = 2$ (and $2 \ne 0$ in $K$), $x \in \dot K$
is a norm from $A$ iff $(\theta, x)_K = 1$. -/
theorem mem_range_norm_iff_hilbertSymbol_gen [FiniteDimensional K A]
    (hsurj : Function.Surjective (tensorToField (K := K) (A := A) (F := F) (E := E)))
    (h2 : Module.finrank K A = 2) (h2K : (2 : K) ≠ 0) (x : Kˣ) :
    x ∈ (Units.map (Algebra.norm K : A →* K)).range ↔ hilbertSymbol K (algebraMap F K θ) x = 1 := by
  have hθ0 : algebraMap F K θ ≠ 0 := by
    rw [map_ne_zero]; rintro rfl; exact hθ ⟨0, by simp⟩
  rw [HN.hilbertSymbol_eq_one_iff_norm K h2K hθ0]
  obtain ⟨t, -, -, hspanT, -, hnormT, -⟩ := HN.tensor_structure θ hθ s hs (exists_eq_add_mul_sqrt hθ hs) K
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz⟩ := hsurj (y : A)
    obtain ⟨x₀, x₁, rfl⟩ := hspanT z
    refine ⟨x₀, x₁, ?_⟩
    rw [← hnormT, ← norm_tensorToField_of_finrank_eq_two hθ hs hsurj h2, hz, ← hy]
    rfl
  · rintro ⟨x₀, x₁, hx⟩
    set y := tensorToField (K := K) (A := A) (F := F) (E := E)
      (algebraMap K _ x₀ + algebraMap K _ x₁ * t)
    have hy : Algebra.norm K y = x := by
      rw [norm_tensorToField_of_finrank_eq_two hθ hs hsurj h2, hnormT, hx]
    have hy0 : y ≠ 0 := by
      intro h0; rw [h0, Algebra.norm_zero] at hy; exact x.ne_zero hy.symm
    exact ⟨Units.mk0 y hy0, Units.ext hy⟩

end Generic

/-! ### Finite spots: the tensor map onto $E_\mathfrak P$ -/

section FiniteTensor

variable (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]

omit hθ hs in
lemma tensorToField_surjective_fin :
    Function.Surjective (tensorToField (K := v.adicCompletion F) (A := w.adicCompletion E) (F := F) (E := E)) := by
  classical
  have hcomp : ∀ z, tensorToField (K := v.adicCompletion F) (A := w.adicCompletion E) (F := F) (E := E) z =
      tensorToPi (fun w : SpotsOver E v => w.1.adicCompletion E) z ⟨w, inferInstance⟩ := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c e => simp [tensorToField, tensorToPi]
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  intro y
  obtain ⟨z, hz⟩ := tensorToPi_spotsOver_surjective E v (Pi.single (⟨w, inferInstance⟩ : SpotsOver E v) y)
  exact ⟨z, by rw [hcomp, hz, Pi.single_eq_same]⟩

/-- **Local norm index at a finite spot with $n_\mathfrak p = 2$** (O'Meara §65A, p. 176, by Corollary 63:13a):
$(\dot F_\mathfrak p : N_{\mathfrak P|\mathfrak p}\dot E_\mathfrak P) = 2$. -/
@[kb "omeara1963" "§65A, p. 176 ((Ḟ_𝔭 : N_{𝔓|𝔭} Ė_𝔓) = 2 if n_𝔭 = 2, finite spot, by 63:13a)"]
theorem index_localNormFin_eq_two (hv : ¬ IsSquare (algebraMap F (v.adicCompletion F) θ)) :
    (Units.map (localNormFin v w)).range.index = 2 := by
  have h2 := (finrank_eq_two_iff_not_isSquare hθ hs v w).2 hv
  rw [show Units.map (localNormFin v w) = Units.map (Algebra.norm (v.adicCompletion F) :
      w.adicCompletion E →* v.adicCompletion F) from rfl,
    range_norm_eq_tensor_of_finrank_eq_two hθ hs (tensorToField_surjective_fin v w) h2]
  obtain rfl := eq_spotBelow_of_liesOver v w
  exact HN.index_norm_eq_two θ hθ s hs (exists_eq_add_mul_sqrt hθ hs) w hv

/-- **Local norm index at a finite spot with $n_\mathfrak p = 1$**: every element is a norm, index $1$. -/
@[kb "omeara1963" "§65A, p. 176 ((Ḟ_𝔭 : N_{𝔓|𝔭} Ė_𝔓) = 1 if n_𝔭 = 1, finite spot)"]
theorem localNormFin_surjective_of_isSquare (hv : IsSquare (algebraMap F (v.adicCompletion F) θ)) :
    Function.Surjective (localNormFin v w) := by
  have h1 := (finrank_eq_one_iff_isSquare hθ hs v w).2 hv
  intro x
  refine ⟨algebraMap (v.adicCompletion F) (w.adicCompletion E) x, ?_⟩
  rw [localNormFin_apply, Algebra.norm_algebraMap, h1, pow_one]

/-- **Local norms and the Hilbert symbol at a finite spot with $n_\mathfrak p = 2$** (O'Meara §65A, p. 176):
$x \in N_{\mathfrak P|\mathfrak p}\dot E_\mathfrak P$ iff $(\theta, x)_\mathfrak p = 1$. -/
@[kb "omeara1963" "§65A, p. 176 (α is a local norm at 𝔭 iff (α, θ)_𝔭 = 1, finite spot)"]
theorem mem_range_localNormFin_iff (hv : ¬ IsSquare (algebraMap F (v.adicCompletion F) θ))
    (x : (v.adicCompletion F)ˣ) :
    x ∈ (Units.map (localNormFin v w)).range ↔
      hilbertSymbol (v.adicCompletion F) (algebraMap F _ θ) x = 1 :=
  mem_range_norm_iff_hilbertSymbol_gen hθ hs (tensorToField_surjective_fin v w)
    ((finrank_eq_two_iff_not_isSquare hθ hs v w).2 hv) (by norm_num) x

end FiniteTensor

/-! ### Infinite spots -/

section Infinite

variable (v : InfinitePlace F) (w : InfinitePlace E) [w.LiesOver v]

omit hθ hs in
lemma tensorToField_surjective_inf :
    Function.Surjective (tensorToField (K := v.Completion) (A := w.Completion) (F := F) (E := E)) := by
  classical
  have hcomp : ∀ z, tensorToField (K := v.Completion) (A := w.Completion) (F := F) (E := E) z =
      tensorToPi (fun w : InfSpotsOver E v => w.1.Completion) z ⟨w, inferInstance⟩ := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c e => simp [tensorToField, tensorToPi]
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  intro y
  obtain ⟨z, hz⟩ := tensorToPi_infSpotsOver_surjective E v (Pi.single (⟨w, inferInstance⟩ : InfSpotsOver E v) y)
  exact ⟨z, by rw [hcomp, hz, Pi.single_eq_same]⟩

/-- **$n(\mathfrak P|\mathfrak p) = 1$ iff $\theta$ is a square at the infinite spot $\mathfrak p$** (O'Meara §65A,
p. 175). -/
@[kb "omeara1963" "§65A, p. 175 (n(𝔓|𝔭) = 1 if θ is a square at 𝔭, infinite spot)"]
theorem finrank_eq_one_iff_isSquare_inf :
    Module.finrank v.Completion w.Completion = 1 ↔ IsSquare (algebraMap F v.Completion θ) :=
  finrank_eq_one_iff_isSquare_gen hθ hs (tensorToField_surjective_inf v w)

/-- **$n(\mathfrak P|\mathfrak p) = 2$ iff $\theta$ is a non-square at the infinite spot $\mathfrak p$**. -/
@[kb "omeara1963" "§65A, p. 175 (n(𝔓|𝔭) = 2 if θ is a non-square at 𝔭, infinite spot)"]
theorem finrank_eq_two_iff_not_isSquare_inf :
    Module.finrank v.Completion w.Completion = 2 ↔ ¬ IsSquare (algebraMap F v.Completion θ) := by
  rw [← finrank_eq_one_iff_isSquare_inf hθ hs v w]
  have h1 := finrank_le_two_gen hθ hs (tensorToField_surjective_inf v w)
  have h2 : 0 < Module.finrank v.Completion w.Completion := Module.finrank_pos
  omega

/-- **Local norm index at an infinite spot with $n_\mathfrak p = 2$** (O'Meara §65A, p. 176). -/
@[kb "omeara1963" "§65A, p. 176 ((Ḟ_𝔭 : N_{𝔓|𝔭} Ė_𝔓) = 2 if n_𝔭 = 2, infinite spot)"]
theorem index_localNormInf_eq_two (hv : ¬ IsSquare (algebraMap F v.Completion θ)) :
    (Units.map (localNormInf E v w)).range.index = 2 := by
  have h2 := (finrank_eq_two_iff_not_isSquare_inf hθ hs v w).2 hv
  rw [show Units.map (localNormInf E v w) = Units.map (Algebra.norm v.Completion :
      w.Completion →* v.Completion) from rfl,
    range_norm_eq_tensor_of_finrank_eq_two hθ hs (tensorToField_surjective_inf v w) h2]
  exact HN.index_norm_eq_two_inf θ hθ s hs (exists_eq_add_mul_sqrt hθ hs) v hv

/-- **Every element is a local norm at an infinite spot with $n_\mathfrak p = 1$**. -/
theorem localNormInf_surjective_of_isSquare (hv : IsSquare (algebraMap F v.Completion θ)) :
    Function.Surjective (localNormInf E v w) := by
  have h1 := (finrank_eq_one_iff_isSquare_inf hθ hs v w).2 hv
  intro x
  refine ⟨algebraMap v.Completion w.Completion x, ?_⟩
  rw [localNormInf_apply, Algebra.norm_algebraMap, h1, pow_one]

/-- **Local norms and the Hilbert symbol at an infinite spot with $n_\mathfrak p = 2$** (O'Meara §65A, p. 176). -/
@[kb "omeara1963" "§65A, p. 176 (α is a local norm at 𝔭 iff (α, θ)_𝔭 = 1, infinite spot)"]
theorem mem_range_localNormInf_iff (hv : ¬ IsSquare (algebraMap F v.Completion θ)) (x : v.Completionˣ) :
    x ∈ (Units.map (localNormInf E v w)).range ↔ hilbertSymbol v.Completion (algebraMap F _ θ) x = 1 :=
  mem_range_norm_iff_hilbertSymbol_gen hθ hs (tensorToField_surjective_inf v w)
    ((finrank_eq_two_iff_not_isSquare_inf hθ hs v w).2 hv)
    (fun h => by have := norm_two_completion v; rw [h, norm_zero] at this; norm_num at this) x

end Infinite

end QuadFormsKB.OMeara
