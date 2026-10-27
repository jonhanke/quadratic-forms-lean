import QuadFormsKB.Tamagawa.BinaryNormOne
import QuadFormsKB.Binary.RelClassNumber

/-!
# Coordinates $F^2 \simeq E = F(\sqrt{-D})$ for $\langle 1, D\rangle$

**Layer:** $F$ a number field, $E/F$ quadratic with nontrivial automorphism $\sigma$ (`Binary.Rel.conj`), $D \in \mathcal O_F$, $D \ne 0$,
and $\theta \in E$ with $\theta^2 = -D$, $\sigma\theta = -\theta$ (`SqrtData`; for $\langle1,D\rangle$ totally positive definite such an
$E$ exists by `exists_sqrtExt_of_not_isSquare`, and it is a CM extension).

**Defines** the coordinate isomorphism $c : F^2 \to E$, $c(x) = x_0 + x_1\theta$ (`cE`, `coordEquiv`), under which
* the norm is $\langle1,D\rangle$: $N_{E/F}(c(x)) = x_0^2 + Dx_1^2$ (`norm_cE`);
* multiplication by $a + b\theta$ is the rotation matrix $\begin{pmatrix}a&-Db\\b&a\end{pmatrix}$ (`cE_rotMat`), and $\sigma$ is
  $\mathrm{diag}(1,-1)$ (`conj_cE`);
* an $\mathcal O_F$-submodule $A \subseteq E$ becomes the lattice `latOf A` $= c^{-1}(A)$; for $A = \mathcal O_E$ this is the lattice
  `latE` of the maximal order, which contains $\mathcal O_F^2$ (the order $\mathcal O_F[\theta]$) and is contained in $(2D)^{-1}\mathcal O_F^2$.

Source: Shimura 2010, §4 (orders of CM fields and their norm forms) [unverified].
-/

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.BinaryCM

open Lattices QuadForm QuadFormsKB.HilbertModular Binary.Rel BinaryNormOne

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

/-- **A square root of $-D$ in $E$** with $\sigma\theta = -\theta$ ($D \ne 0$), the generator of the order $\mathcal O_F[\theta]$. -/
structure SqrtData (D : 𝓞 F) (E : Type) [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E] where
  /-- the square root $\theta$ -/
  θ : E
  sq : θ ^ 2 = -algebraMap F E (algebraMap (𝓞 F) F D)
  conj_eq : conj F E θ = -θ
  D_ne : D ≠ 0

variable {D : 𝓞 F} (S : SqrtData D E)

/-- $D$ as an element of $F$. -/
abbrev dF (D : 𝓞 F) : F := algebraMap (𝓞 F) F D

include S in
theorem dF_ne_zero : dF D ≠ 0 :=
  (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr S.D_ne

theorem θ_ne_zero : S.θ ≠ 0 := by
  intro h
  have := S.sq
  rw [h, zero_pow two_ne_zero, eq_comm, neg_eq_zero, map_eq_zero_iff _ (algebraMap F E).injective] at this
  exact dF_ne_zero S this

theorem θ_sq : S.θ * S.θ = -algebraMap F E (dF D) := by rw [← sq]; exact S.sq

/-! ### The coordinate map -/

/-- **The coordinates** $c(x) = x_0 + x_1\theta$. -/
def cE (x : Fin 2 → F) : E := algebraMap F E (x 0) + algebraMap F E (x 1) * S.θ

theorem cE_add (x y : Fin 2 → F) : cE S (x + y) = cE S x + cE S y := by
  simp only [cE, Pi.add_apply, map_add]; ring

theorem cE_smul (a : F) (x : Fin 2 → F) : cE S (a • x) = algebraMap F E a * cE S x := by
  simp only [cE, Pi.smul_apply, smul_eq_mul, map_mul]; ring

theorem cE_zero : cE S 0 = 0 := by simp [cE]

theorem conj_cE (x : Fin 2 → F) : conj F E (cE S x) = cE S ![x 0, -x 1] := by
  simp only [cE, map_add, map_mul, AlgEquiv.commutes, S.conj_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, map_neg]
  ring

/-- **The norm is $\langle1,D\rangle$:** $N_{E/F}(x_0 + x_1\theta) = x_0^2 + Dx_1^2$. -/
theorem norm_cE (x : Fin 2 → F) : Algebra.norm F (cE S x) = x 0 ^ 2 + dF D * x 1 ^ 2 := by
  apply (algebraMap F E).injective
  rw [algebraMap_norm, conj_cE]
  simp only [cE, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, map_add, map_mul, map_pow,
    map_neg]
  have := θ_sq S
  linear_combination (-(algebraMap F E (x 1)) ^ 2) * this

theorem norm_cE_eq_eval (x : Fin 2 → F) : Algebra.norm F (cE S x) = (formF (diagForm1 D)).eval x := by
  rw [norm_cE, eval_formF_diag]

theorem cE_injective : Function.Injective (cE S) := by
  intro x y h
  have h2 := congrArg (conj F E) h
  rw [conj_cE, conj_cE] at h2
  simp only [cE, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, map_neg] at h h2
  have hθ := θ_ne_zero S
  have e1 : algebraMap F E (x 1) = algebraMap F E (y 1) := by
    have : (2 * S.θ) * (algebraMap F E (x 1) - algebraMap F E (y 1)) = 0 := by linear_combination h - h2
    have h2θ : 2 * S.θ ≠ 0 := mul_ne_zero two_ne_zero hθ
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h2θ)
  have e0 : algebraMap F E (x 0) = algebraMap F E (y 0) := by
    rw [e1] at h; linear_combination h
  ext i; fin_cases i
  · exact (algebraMap F E).injective e0
  · exact (algebraMap F E).injective e1

theorem exists_cE_eq (z : E) : ∃ x : Fin 2 → F, cE S x = z := by
  have := charZero_top F E
  have hθ := θ_ne_zero S
  obtain ⟨a, ha⟩ := (conj_eq_self_iff (F := F) (z + conj F E z)).mp (by rw [map_add, conj_conj, add_comm])
  obtain ⟨b, hb⟩ := (conj_eq_self_iff (F := F) ((z - conj F E z) / S.θ)).mp (by
    rw [map_div₀, map_sub, conj_conj, S.conj_eq]; field_simp; ring)
  refine ⟨![a / 2, b / 2], ?_⟩
  simp only [cE, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, map_div₀, ha, hb,
    map_ofNat]
  field_simp
  ring

/-- **The coordinate isomorphism** $F^2 \simeq E$, $x \mapsto x_0 + x_1\theta$. -/
def coordEquiv : (Fin 2 → F) ≃ₗ[F] E :=
  LinearEquiv.ofBijective
    { toFun := cE S
      map_add' := cE_add S
      map_smul' := fun a x => by rw [cE_smul, RingHom.id_apply, Algebra.smul_def] }
    ⟨cE_injective S, fun z => exists_cE_eq S z⟩

theorem coordEquiv_apply (x : Fin 2 → F) : coordEquiv S x = cE S x := rfl

/-- The coordinate map as an $\mathcal O_F$-linear map. -/
abbrev cLin : (Fin 2 → F) →ₗ[𝓞 F] E := (coordEquiv S).toLinearMap.restrictScalars (𝓞 F)

theorem cLin_apply (x : Fin 2 → F) : cLin S x = cE S x := rfl

/-! ### Multiplication and conjugation in coordinates -/

/-- **Multiplication by $a + b\theta$ is the rotation matrix** $\begin{pmatrix}a&-Db\\b&a\end{pmatrix}$:
$c(\mathrm{rotMat}(D,a,b,1)\,y) = (a + b\theta)\,c(y)$. -/
theorem cE_rotMat (a b : F) (y : Fin 2 → F) :
    cE S (rotMat (dIn D F) a b 1 *ᵥ y) = cE S ![a, b] * cE S y := by
  have := θ_sq S
  simp only [cE, rotMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
    Matrix.cons_val_fin_one, map_add, map_mul, map_neg, mul_one, dIn, Algebra.algebraMap_self, RingHom.id_apply]
  rw [dF] at this
  linear_combination (-(algebraMap F E b * algebraMap F E (y 1))) * this

/-- **$\sigma$ in coordinates** is $\mathrm{diag}(1,-1) = \mathrm{rotMat}(D,1,0,-1)$. -/
theorem cE_rotMat_conj (y : Fin 2 → F) :
    cE S (rotMat (dIn D F) 1 0 (-1) *ᵥ y) = conj F E (cE S y) := by
  rw [conj_cE]
  congr 1
  ext i; fin_cases i <;> simp [rotMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **A rotation-reflection in coordinates:** $c(\mathrm{rotMat}(D,a,b,s)\,y) = (a+b\theta)\,c(y)$ for $s = 1$ and
$(a+b\theta)\,\sigma(c(y))$ for $s = -1$. -/
theorem rotMat_neg_eq (a b : F) :
    rotMat (dIn D F) a b (-1) = rotMat (dIn D F) a b 1 * rotMat (dIn D F) 1 0 (-1) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotMat, Matrix.mul_apply, Fin.sum_univ_two]

/-! ### Lattices of $\mathcal O_F$-submodules of $E$ -/

/-- **The lattice of an $\mathcal O_F$-submodule** $A \subseteq E$ in coordinates: $c^{-1}(A) \subseteq F^2$. -/
def latOf (A : Submodule (𝓞 F) E) : Submodule (𝓞 F) (Fin 2 → F) := A.comap (cLin S)

theorem mem_latOf {A : Submodule (𝓞 F) E} {x : Fin 2 → F} : x ∈ latOf S A ↔ cE S x ∈ A := Iff.rfl

theorem latOf_mono {A B : Submodule (𝓞 F) E} (h : A ≤ B) : latOf S A ≤ latOf S B :=
  Submodule.comap_mono h

/-- **The lattice of the maximal order** $\mathcal O_E$ in coordinates. -/
abbrev latE : Submodule (𝓞 F) (Fin 2 → F) := latOf S (idealLat F (⊤ : Ideal (𝓞 E)))

theorem mem_latE {x : Fin 2 → F} : x ∈ latE S ↔ IsIntegral ℤ (cE S x) := by
  rw [latE, mem_latOf, mem_idealLat]
  constructor
  · rintro ⟨a, -, ha⟩; rw [← ha]; exact a.2
  · intro h; exact ⟨⟨cE S x, h⟩, Submodule.mem_top, rfl⟩

theorem isIntegral_θ : IsIntegral ℤ S.θ := by
  have hD : IsIntegral ℤ (algebraMap F E (dF D)) := by
    rw [dF, ← algebraMap_O_E]
    exact (algebraMap (𝓞 F) (𝓞 E) D).2
  have h2 : IsIntegral ℤ (S.θ ^ 2) := by rw [S.sq]; exact hD.neg
  exact IsIntegral.of_pow two_pos h2

theorem isIntegral_algebraMap_int (a : 𝓞 F) : IsIntegral ℤ (algebraMap F E (algebraMap (𝓞 F) F a)) := by
  rw [← algebraMap_O_E]
  exact (algebraMap (𝓞 F) (𝓞 E) a).2

/-- **$\mathcal O_F^2 \subseteq$ `latE`**: the order $\mathcal O_F[\theta]$ lies in $\mathcal O_E$. -/
theorem intVec_le_latE : (intVec : Submodule (𝓞 F) (Fin 2 → F)) ≤ latE S := by
  intro x hx
  rw [mem_latE]
  obtain ⟨a, ha⟩ := hx 0
  obtain ⟨b, hb⟩ := hx 1
  rw [cE, ← ha, ← hb]
  exact (isIntegral_algebraMap_int a).add ((isIntegral_algebraMap_int b).mul (isIntegral_θ S))

/-- Integral elements of $E$ have integral trace and norm. -/
theorem trace_mem_of_isIntegral {z : E} (hz : IsIntegral ℤ z) :
    Algebra.trace F E z ∈ (algebraMap (𝓞 F) F).range := by
  have h1 : IsIntegral ℤ (Algebra.trace F E z) := Algebra.isIntegral_trace (R := ℤ) hz
  exact ⟨⟨_, h1⟩, rfl⟩

theorem norm_mem_of_isIntegral {z : E} (hz : IsIntegral ℤ z) :
    Algebra.norm F z ∈ (algebraMap (𝓞 F) F).range := by
  have h1 : IsIntegral ℤ (Algebra.norm F z) := Algebra.isIntegral_norm (R := ℤ) F hz
  exact ⟨⟨_, h1⟩, rfl⟩

theorem trace_cE (x : Fin 2 → F) : Algebra.trace F E (cE S x) = 2 * x 0 := by
  apply (algebraMap F E).injective
  rw [algebraMap_trace, conj_cE]
  simp [cE, map_ofNat]; ring

theorem trace_cE_mul_θ (x : Fin 2 → F) : Algebra.trace F E (cE S x * S.θ) = -2 * dF D * x 1 := by
  apply (algebraMap F E).injective
  rw [algebraMap_trace, map_mul, conj_cE, S.conj_eq]
  have := θ_sq S
  simp [cE, map_ofNat]
  linear_combination (2 * algebraMap F E (x 1)) * this

/-- **`latE` $\subseteq (2D)^{-1}\mathcal O_F^2$:** for $x_0 + x_1\theta \in \mathcal O_E$, $2x_0 = \mathrm{Tr}(z)$ and
$-2Dx_1 = \mathrm{Tr}(z\theta)$ are integral. -/
theorem smul_mem_intVec_of_mem_latE {x : Fin 2 → F} (hx : x ∈ latE S) : (2 * D) • x ∈ intVec := by
  rw [mem_latE] at hx
  obtain ⟨t, ht⟩ := trace_mem_of_isIntegral (F := F) hx
  obtain ⟨s, hs⟩ := trace_mem_of_isIntegral (F := F) (hx.mul (isIntegral_θ S))
  rw [trace_cE] at ht
  rw [trace_cE_mul_θ] at hs
  intro i; fin_cases i
  · refine ⟨D * t, ?_⟩
    show algebraMap (𝓞 F) F (D * t) = ((2 * D) • x) 0
    rw [Pi.smul_apply, Algebra.smul_def, map_mul, ht, map_mul, map_ofNat]; ring
  · refine ⟨-s, ?_⟩
    show algebraMap (𝓞 F) F (-s) = ((2 * D) • x) 1
    rw [Pi.smul_apply, Algebra.smul_def, map_neg, hs, map_mul, map_ofNat]; ring

include S in
theorem two_mul_ne_zero : (2 * D : 𝓞 F) ≠ 0 := mul_ne_zero two_ne_zero S.D_ne

/-- `latE` is a lattice. -/
theorem latE_isLattice : (latE S).IsLattice F :=
  isLattice_of_global_bounds (two_mul_ne_zero S)
    (fun _ hx => intVec_le_latE S ((intVec : Submodule (𝓞 F) (Fin 2 → F)).smul_mem _ hx))
    (fun _ hx => smul_mem_intVec_of_mem_latE S hx)

/-- The lattice of the maximal order as an element of `Lat F 2`. -/
abbrev latEL : Lat F 2 := ⟨latE S, latE_isLattice S⟩

/-- **`latE` is integral** for $\langle 1, D\rangle$: $Q(x) = N(c(x)) \in \mathcal O_F$. -/
theorem isIntegral_latE : IsIntegral (formF (diagForm1 D)) (latE S) := by
  intro x hx
  rw [mem_latE] at hx
  rw [show (formF (diagForm1 D)).evalIn F x = (formF (diagForm1 D)).eval x from rfl, ← norm_cE_eq_eval S]
  exact norm_mem_of_isIntegral hx

/-- At primes $\mathfrak p \nmid 2D$, `latE` is locally $\mathcal O_F^2$ (the order $\mathcal O_F[\theta]$ is maximal there). -/
theorem loc_latE_of_not_mem (v : HeightOneSpectrum (𝓞 F)) (hv : (2 * D : 𝓞 F) ∉ v.asIdeal) :
    loc v (latE S) = std v :=
  loc_eq_std_of_not_mem v
    (fun _ hx => intVec_le_latE S ((intVec : Submodule (𝓞 F) (Fin 2 → F)).smul_mem _ hx))
    (fun _ hx => smul_mem_intVec_of_mem_latE S hx) hv

end QuadFormsKB.Tamagawa.BinaryCM
