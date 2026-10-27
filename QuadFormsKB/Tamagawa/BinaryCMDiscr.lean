import QuadFormsKB.Tamagawa.BinaryCMConstants

/-!
# The discriminant of $E = F(\sqrt{-D})$ and the conductor of $\mathcal O_F[\sqrt{-D}]$

**Layer:** $E = F(\theta)$, $\theta^2 = -D$ (`SqrtData`), $\theta_O = \theta \in \mathcal O_E$, $R = \mathcal O_F[\theta]$, $\mathfrak f = \{y \in \mathcal O_E : y\mathcal O_E \subseteq R\}$
(Mathlib's `conductor`), $\mathfrak D_{E/F}$ the different, $n = [F:\mathbb Q]$.

**Proves**
* `minpoly_θ`: the minimal polynomial of $\theta$ is $X^2 + D$; `aeval_derivative_minpoly`: $f'(\theta) = 2\theta$;
* **`discr_mul_absNorm_conductor`**: $|d_E|\cdot N(\mathfrak f) = 4^n\,|d_F|^2\,|N_{F/\mathbb Q}D|$, from Mathlib's
  `natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow` ($|d_E| = N(\mathfrak D_{E/F})\,|d_F|^2$) and `conductor_mul_differentIdeal`
  ($\mathfrak f\,\mathfrak D_{E/F} = (f'(\theta)) = (2\theta)$), $N(2\theta) = N_{F/\mathbb Q}(4D)$.

Source: Neukirch 1999, Ch. III §2, Prop. 2.4 and Thm. 2.9 (different and conductor) [unverified locator].

-/

open NumberField Polynomial IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.BinaryCM

open Binary.Rel

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

variable {D : 𝓞 F} (S : SqrtData D E)

/-! ### The generator $\theta$ and its minimal polynomial -/

/-- $\theta$ as an element of $\mathcal O_E$. -/
def θO : 𝓞 E := ⟨S.θ, isIntegral_θ S⟩

theorem coe_θO : ((θO S : 𝓞 E) : E) = S.θ := rfl

theorem adjoin_θ_eq_top : Algebra.adjoin F {S.θ} = ⊤ := by
  rw [eq_top_iff]; intro y _
  rw [← cE_coordOf S y]
  exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _)
    (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Algebra.self_mem_adjoin_singleton F S.θ))

theorem θ_not_mem_range : S.θ ∉ (algebraMap F E).range := by
  rintro ⟨f, hf⟩
  have h1 : conj F E S.θ = S.θ := by rw [← hf, AlgEquiv.commutes]
  rw [S.conj_eq] at h1
  have h0 : S.θ = 0 := by
    have : (2 : E) * S.θ = 0 := by linear_combination -h1
    exact (mul_eq_zero.mp this).resolve_left two_ne_zero
  have h2 := S.sq
  rw [h0, zero_pow two_ne_zero, eq_comm, neg_eq_zero] at h2
  have : algebraMap (𝓞 F) F D = 0 := (algebraMap F E).injective (by rw [h2, map_zero])
  exact S.D_ne ((map_eq_zero_iff _ RingOfIntegers.coe_injective).mp this)

/-- **The minimal polynomial of $\theta$ over $F$ is $X^2 + D$.** -/
theorem minpoly_θ : minpoly F S.θ = X ^ 2 + C (dF D) := by
  have hint : IsIntegral F S.θ := Algebra.IsIntegral.isIntegral _
  have hmon : (X ^ 2 + C (dF D) : F[X]).Monic := monic_X_pow_add_C _ two_ne_zero
  have haeval : aeval S.θ (X ^ 2 + C (dF D) : F[X]) = 0 := by
    simp only [map_add, map_pow, aeval_X, aeval_C, S.sq, dF]; ring
  have hdvd := minpoly.dvd F S.θ haeval
  have hle : (minpoly F S.θ).natDegree ≤ 2 := by
    have := natDegree_le_of_dvd hdvd hmon.ne_zero
    rwa [natDegree_X_pow_add_C] at this
  have hne1 : (minpoly F S.θ).natDegree ≠ 1 := fun h => θ_not_mem_range S (minpoly.natDegree_eq_one_iff.mp h)
  have hpos := minpoly.natDegree_pos hint
  refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmon hdvd ?_).symm
  rw [natDegree_X_pow_add_C]; omega

/-- **$f'(\theta) = 2\theta$** for the minimal polynomial $f$ of $\theta$ over $\mathcal O_F$. -/
theorem aeval_derivative_minpoly :
    aeval (θO S) (derivative (minpoly (𝓞 F) (θO S))) = 2 * θO S := by
  apply RingOfIntegers.coe_injective
  have hs : IsIntegral (𝓞 F) (θO S) := IsIntegral.of_finite (𝓞 F) (θO S)
  have h := minpoly.isIntegrallyClosed_eq_field_fractions F E hs
  rw [show algebraMap (𝓞 E) E (θO S) = S.θ from rfl, minpoly_θ] at h
  show algebraMap (𝓞 E) E _ = algebraMap (𝓞 E) E _
  rw [← aeval_algebraMap_apply, show algebraMap (𝓞 E) E (θO S) = S.θ from rfl,
    ← aeval_map_algebraMap F, ← derivative_map, ← h, map_mul, map_ofNat, show algebraMap (𝓞 E) E (θO S) = S.θ from rfl]
  simp only [derivative_add, derivative_X_pow, derivative_C, add_zero, map_mul, map_natCast, aeval_X]
  norm_num

/-! ### $|d_E|\,N(\mathfrak f) = 4^n|d_F|^2|N D|$ -/

/-- $N_{E/\mathbb Q}(2\theta) = 4^n N_{F/\mathbb Q}(D)$. -/
theorem norm_two_θ :
    Algebra.norm ℚ (2 * S.θ) = 4 ^ Module.finrank ℚ F * Algebra.norm ℚ (dF D) := by
  have h2 : 2 * S.θ = cE S ![0, 2] := by
    simp only [cE, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, map_zero, zero_add, map_ofNat]
  rw [← Algebra.norm_norm (S := F), h2, norm_cE]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [show (0 : F) ^ 2 + dF D * 2 ^ 2 = algebraMap ℚ F 4 * dF D by rw [map_ofNat]; ring, map_mul,
    Algebra.norm_algebraMap]

/-- **The discriminant and the conductor:** $|d_E|\cdot N(\mathfrak f) = 4^n\,|d_F|^2\,|N_{F/\mathbb Q}D|$, $\mathfrak f$ the conductor of
$\mathcal O_F[\theta]$ in $\mathcal O_E$. -/
@[kb "neukirch1999" "Ch. III §2, Prop. 2.4, Thm. 2.9 (different, conductor, discriminant) [unverified]"]
theorem discr_mul_absNorm_conductor :
    |(discr E : ℝ)| * (Ideal.absNorm (conductor (𝓞 F) (θO S)) : ℝ) =
      4 ^ Module.finrank ℚ F * |(discr F : ℝ)| ^ 2 * |(Algebra.norm ℚ (dF D) : ℝ)| := by
  have h1 := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) E (𝓞 E)
  rw [Algebra.IsQuadraticExtension.finrank_eq_two F E] at h1
  have hx : Algebra.adjoin F {algebraMap (𝓞 E) E (θO S)} = ⊤ := adjoin_θ_eq_top S
  have h2 := congrArg Ideal.absNorm (conductor_mul_differentIdeal (𝓞 F) F E (θO S) hx)
  rw [aeval_derivative_minpoly, map_mul, Ideal.absNorm_span_singleton] at h2
  have h3 : ((Algebra.norm ℤ (2 * θO S) : ℤ) : ℚ) = 4 ^ Module.finrank ℚ F * Algebra.norm ℚ (dF D) := by
    rw [Algebra.coe_norm_int]
    have : (((2 * θO S : 𝓞 E)) : E) = 2 * S.θ := by push_cast; rfl
    rw [this, norm_two_θ]
  have e1 : |(discr E : ℝ)| = (Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 E)) : ℝ) * |(discr F : ℝ)| ^ 2 := by
    rw [← Int.cast_abs, ← Int.cast_abs, ← Int.natCast_natAbs, ← Int.natCast_natAbs, h1]; push_cast; ring
  have e2 : (Ideal.absNorm (conductor (𝓞 F) (θO S)) : ℝ) * Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 E)) =
      4 ^ Module.finrank ℚ F * |(Algebra.norm ℚ (dF D) : ℝ)| := by
    have : ((Ideal.absNorm (conductor (𝓞 F) (θO S)) * Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 E)) : ℕ) : ℝ) =
        |((Algebra.norm ℤ (2 * θO S) : ℤ) : ℝ)| := by
      rw [h2, Nat.cast_natAbs, Int.cast_abs]
    push_cast at this
    rw [this]
    have h3' : ((Algebra.norm ℤ (2 * θO S) : ℤ) : ℝ) = 4 ^ Module.finrank ℚ F * (Algebra.norm ℚ (dF D) : ℝ) := by
      have := congrArg (fun q : ℚ => (q : ℝ)) h3
      push_cast at this
      exact this
    rw [h3', abs_mul, abs_of_pos (by positivity)]
  rw [e1]
  linear_combination |(discr F : ℝ)| ^ 2 * e2

/-! ### The conductor in coordinates -/

open Lattices Matrix BinaryNormOne

theorem coordOf_algebraMap (r : F) : coordOf S (algebraMap F E r) = ![r, 0] := by
  rw [← coordOf_cE S ![r, 0]]; congr 1; simp [cE]

theorem coordOf_θ : coordOf S S.θ = ![0, 1] := by
  rw [← coordOf_cE S ![0, 1]]; congr 1; simp [cE]

theorem coordOf_mul (x y : E) : coordOf S (x * y) = mulMat S x *ᵥ coordOf S y := by
  rw [← coordOf_cE S (mulMat S x *ᵥ coordOf S y), cE_mulMat, cE_coordOf]

theorem coordOf_add (x y : E) : coordOf S (x + y) = coordOf S x + coordOf S y :=
  map_add (coordEquiv S).symm x y

theorem mulMat_algebraMap_mulVec (a : F) (x : Fin 2 → F) : mulMat S (algebraMap F E a) *ᵥ x = a • x := by
  rw [← coordOf_cE S (mulMat S _ *ᵥ x), cE_mulMat, ← cE_smul, coordOf_cE]

theorem mem_range_of_mem_intVec {x : Fin 2 → F} (hx : x ∈ intVec) (i : Fin 2) :
    x i ∈ (algebraMap (𝓞 F) F).range := mem_intVec.mp hx i

theorem mulMat_mulVec_mem_intVec {x : E} (hx : coordOf S x ∈ intVec) {y : Fin 2 → F} (hy : y ∈ intVec) :
    mulMat S x *ᵥ y ∈ intVec := by
  have hd : dIn D F ∈ (algebraMap (𝓞 F) F).range := ⟨D, rfl⟩
  rw [mulMat, rotMat_mulVec_eq, mem_intVec]
  have h0 := mem_range_of_mem_intVec hx 0
  have h1 := mem_range_of_mem_intVec hx 1
  have g0 := mem_range_of_mem_intVec hy 0
  have g1 := mem_range_of_mem_intVec hy 1
  intro i; fin_cases i
  · exact Subring.sub_mem _ (Subring.mul_mem _ h0 g0) (Subring.mul_mem _ (Subring.mul_mem _ hd h1) g1)
  · exact Subring.add_mem _ (Subring.mul_mem _ h1 g0) (Subring.mul_mem _ h0 g1)

/-- **$\mathcal O_F[\theta]$ in coordinates:** $u \in \mathcal O_F[\theta]$ iff its coordinates are integral. -/
theorem mem_adjoin_iff (u : 𝓞 E) :
    u ∈ Algebra.adjoin (𝓞 F) {θO S} ↔ coordOf S (u : E) ∈ intVec := by
  constructor
  · intro hu
    induction hu using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff.mp hx, coe_θO, coordOf_θ, mem_intVec]
      intro i; fin_cases i
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
    | algebraMap r =>
      show coordOf S (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) r)) ∈ intVec
      rw [algebraMap_O_E, coordOf_algebraMap, mem_intVec]
      intro i; fin_cases i
      · exact ⟨r, rfl⟩
      · exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      rw [show ((x + y : 𝓞 E) : E) = (x : E) + y from rfl, coordOf_add]
      exact Submodule.add_mem _ hx hy
    | mul x y _ _ hx hy =>
      rw [show ((x * y : 𝓞 E) : E) = (x : E) * y from rfl, coordOf_mul]
      exact mulMat_mulVec_mem_intVec S hx hy
  · intro h
    obtain ⟨c0, hc0⟩ := mem_range_of_mem_intVec h 0
    obtain ⟨c1, hc1⟩ := mem_range_of_mem_intVec h 1
    have hu : u = algebraMap (𝓞 F) (𝓞 E) c0 + algebraMap (𝓞 F) (𝓞 E) c1 * θO S := by
      apply RingOfIntegers.coe_injective
      show (u : E) = algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) c0 + algebraMap (𝓞 F) (𝓞 E) c1 * θO S)
      rw [map_add, map_mul, algebraMap_O_E, algebraMap_O_E, hc0, hc1,
        show algebraMap (𝓞 E) E (θO S) = S.θ from rfl]
      conv_lhs => rw [← cE_coordOf S (u : E)]
      rfl
    rw [hu]
    exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Algebra.self_mem_adjoin_singleton _ _))

/-- **The conductor in coordinates:** $y \in \mathfrak f$ iff multiplication by $y$ maps $L_E$ into $\mathcal O_F^2$. -/
theorem mem_conductor_iff' (y : 𝓞 E) :
    y ∈ conductor (𝓞 F) (θO S) ↔ ∀ x ∈ latE S, mulMat S (y : E) *ᵥ x ∈ intVec := by
  show (∀ b : 𝓞 E, y * b ∈ Algebra.adjoin (𝓞 F) {θO S}) ↔ _
  constructor
  · intro h x hx
    have hb := (mem_adjoin_iff S _).mp (h ⟨cE S x, (mem_latE S).mp hx⟩)
    rwa [show ((y * ⟨cE S x, (mem_latE S).mp hx⟩ : 𝓞 E) : E) = (y : E) * cE S x from rfl, coordOf_mul,
      coordOf_cE] at hb
  · intro h b
    rw [mem_adjoin_iff, show ((y * b : 𝓞 E) : E) = (y : E) * b from rfl, coordOf_mul]
    refine h _ ((mem_latE S).mpr ?_)
    rw [cE_coordOf]; exact b.2

/-! ### The conductor locally: $\mathfrak f_\mathfrak p = \varpi^{c_\mathfrak p}\Lambda_\mathfrak p$ -/

section Local

open Loc LocalDensity

variable {S}

/-- **Localization of a matrix inclusion:** if $A L \subseteq L'$ then $A L_\mathfrak p \subseteq L'_\mathfrak p$. -/
theorem mulVec_mem_loc' (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} {L L' : Submodule (𝓞 F) (Fin n → F)}
    {A : Matrix (Fin n) (Fin n) F} (hA : ∀ x ∈ L, A *ᵥ x ∈ L') {y : Fin n → v.adicCompletion F} (hy : y ∈ loc v L) :
    A.map (algebraMap F (v.adicCompletion F)) *ᵥ y ∈ loc v L' := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    rw [← locVec_mulVec]
    exact locVec_mem_loc v (hA x hx)
  | zero => rw [mulVec_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [mulVec_add]; exact Submodule.add_mem _ ha hb
  | smul c m _ hm =>
    rw [show (c • m : Fin n → v.adicCompletion F) = (c : v.adicCompletion F) • m from rfl, mulVec_smul]
    exact Submodule.smul_mem _ c hm

theorem e0_mem_intVec : (![1, 0] : Fin 2 → F) ∈ intVec := by
  rw [mem_intVec]; intro i; fin_cases i
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩

/-- **The local shape of the conductor:** if multiplication by $y$ maps $L_E$ into $\mathcal O_F^2$, then at every $\mathfrak p$,
$y = \varphi(w)$ with $\varpi^{c} \mid w_0, w_1$, i.e. $y \in \varpi^c\Lambda_\mathfrak p$ ($y\cdot 1, y\cdot\omega \in \mathfrak o^2$ and
$y\omega = w_1a + (w_0 + bw_1)\omega$). -/
theorem exists_φ_of_conductor {y : Fin 2 → F} (hy : ∀ x ∈ latE S, mulMat S (cE S y) *ᵥ x ∈ intVec)
    {v : HeightOneSpectrum (𝓞 F)} (L : LocData S v) :
    ∃ w : Γ L, φ L w = locVec v y ∧ πv v ^ L.c ∣ w.re ∧ πv v ^ L.c ∣ w.im := by
  have he0 : (![1, 0] : Fin 2 → F) ∈ latE S := intVec_le_latE S e0_mem_intVec
  have hy0 : y ∈ intVec := by
    have := hy _ he0
    rwa [show mulMat S (cE S y) *ᵥ ![1, 0] = y by
      rw [← coordOf_cE S (mulMat S (cE S y) *ᵥ ![1, 0]), cE_mulMat,
        show cE S ![1, 0] = 1 by simp [cE], mul_one, coordOf_cE]] at this
  have hyloc : locVec v y ∈ loc v (latE S) := locVec_mem_loc v (intVec_le_latE S hy0)
  obtain ⟨w, hw⟩ := (mem_loc_iff_φ L _).mp hyloc
  have hstd : φ L w ∈ std v := by rw [hw, ← loc_intVec]; exact locVec_mem_loc v hy0
  have him := (φ_mem_std_iff L w).mp hstd
  have hA := mulVec_mem_loc' v hy (φ_mem L ⟨0, 1⟩)
  rw [loc_intVec, mulMat_map, coordOf_cE] at hA
  have e : rotMat (dIn D (v.adicCompletion F)) (algebraMap F (v.adicCompletion F) (y 0))
      (algebraMap F (v.adicCompletion F) (y 1)) 1 = rotMat (dIn D (v.adicCompletion F)) (φ L w 0) (φ L w 1) 1 := by
    rw [hw]; rfl
  rw [e, φ_mul] at hA
  have hre := (φ_mem_std_iff L _).mp hA
  simp only [QuadraticAlgebra.im_mul, mul_one, mul_zero, add_zero] at hre
  exact ⟨w, hw, (dvd_add_left (Dvd.dvd.mul_left him _)).mp hre, him⟩

end Local

/-! ### The conductor is $\prod_\mathfrak p\mathfrak p^{c_\mathfrak p}\cdot\mathcal O_E$ -/

section Global

open Loc LocalDensity WithZero

variable (U : Finset (HeightOneSpectrum (𝓞 F)))

/-- **The conductor ideal of $\mathcal O_F$:** $\mathfrak c = \prod_{\mathfrak p\in U}\mathfrak p^{c_\mathfrak p}$. -/
def condIdeal : Ideal (𝓞 F) := ∏ v ∈ U, v.asIdeal ^ cv S v

variable {S U}

theorem φ_smul {v : HeightOneSpectrum (𝓞 F)} (L : LocData S v) (r : v.adicCompletionIntegers F) (z : Γ L) :
    φ L (r • z) = (r : v.adicCompletion F) • φ L z := by
  apply vec2_ext
  · rw [Pi.smul_apply, φ_zero', φ_zero']
    simp only [QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, smul_eq_mul]
    push_cast; ring
  · rw [Pi.smul_apply, φ_one', φ_one']
    simp only [QuadraticAlgebra.im_smul, smul_eq_mul]
    push_cast; ring

theorem valued_le_of_mem_condIdeal (hcU : ∀ v ∉ U, cv S v = 0) {a : 𝓞 F} (ha : a ∈ condIdeal S U)
    (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) a) ≤ exp (-(cv S v : ℤ)) := by
  by_cases hv : v ∈ U
  · exact valued_le_of_mem_pow v (Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hv) ha)
  · rw [hcU v hv, Nat.cast_zero, neg_zero, exp_zero]; exact valued_int_le_one v a

/-- $\mathfrak c\,L_E \subseteq \mathcal O_F^2$. -/
theorem smul_mem_intVec_of_mem_condIdeal (hcU : ∀ v ∉ U, cv S v = 0) {a : 𝓞 F} (ha : a ∈ condIdeal S U)
    {x : Fin 2 → F} (hx : x ∈ latE S) : a • x ∈ intVec := by
  rw [mem_iff_forall_loc intVec_isLattice]
  intro v
  rw [loc_intVec, locVec_smul_int]
  set L := locD S v
  obtain ⟨z, hz⟩ := (mem_loc_iff_φ L _).mp (locVec_mem_loc v hx)
  rw [← hz]
  have e : (algebraMap (𝓞 F) (v.adicCompletionIntegers F) a) • φ L z =
      φ L (algebraMap (𝓞 F) (v.adicCompletionIntegers F) a • z) := (φ_smul L _ z).symm
  rw [e, φ_mem_std_iff]
  have hdvd : πv v ^ L.c ∣ algebraMap (𝓞 F) (v.adicCompletionIntegers F) a := by
    rw [← Ideal.mem_span_singleton, NF.mem_span_π_pow]
    exact valued_le_of_mem_condIdeal hcU ha v
  rw [QuadraticAlgebra.im_smul, smul_eq_mul]
  exact Dvd.dvd.mul_right hdvd _

/-- An element of $\mathfrak c$ of exact valuation $c_\mathfrak p$ at $\mathfrak p$ (prime avoidance). -/
theorem exists_mem_condIdeal_valued (hcU : ∀ v ∉ U, cv S v = 0) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ a ∈ condIdeal S U, Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) a) = exp (-(cv S v : ℤ)) := by
  classical
  obtain ⟨π0, hπ0⟩ := v.intValuation_exists_uniformizer
  have hπ0v : π0 ∈ v.asIdeal := by
    rw [← v.intValuation_lt_one_iff_mem, hπ0, ← exp_zero, exp_lt_exp]; norm_num
  have hnot : ¬ (∏ w ∈ U.erase v, w.asIdeal ^ cv S w) ≤ v.asIdeal := by
    intro hle
    obtain ⟨w, hw, hwle⟩ := (Ideal.IsPrime.prod_le v.isPrime).mp hle
    have hwv : w ≠ v := Finset.ne_of_mem_erase hw
    have hwle' : w.asIdeal ≤ v.asIdeal := v.isPrime.le_of_pow_le hwle
    exact hwv (HeightOneSpectrum.ext (w.isMaximal.eq_of_le v.isPrime.ne_top hwle'))
  obtain ⟨t, ht, htv⟩ := SetLike.not_le_iff_exists.mp hnot
  have ht1 : v.intValuation t = 1 :=
    le_antisymm (v.intValuation_le_one t) (not_lt.mp fun h => htv ((v.intValuation_lt_one_iff_mem t).mp h))
  refine ⟨π0 ^ cv S v * t, ?_, ?_⟩
  · by_cases hv : v ∈ U
    · rw [condIdeal, ← Finset.mul_prod_erase U _ hv]
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hπ0v _) ht
    · rw [hcU v hv, pow_zero, one_mul, condIdeal, ← Finset.erase_eq_of_notMem hv]; exact ht
  · simp only [map_mul, map_pow, valued_algebraMap_int, hπ0, ht1, mul_one]
    rw [← WithZero.exp_nsmul]; congr 1; simp

/-- $\mathfrak c\,\Lambda_\mathfrak p \subseteq (\mathfrak cL_E)_\mathfrak p$. -/
theorem smul_mem_loc_condIdeal {a : 𝓞 F} (ha : a ∈ condIdeal S U) {v : HeightOneSpectrum (𝓞 F)}
    {y : Fin 2 → v.adicCompletion F} (hy : y ∈ loc v (latE S)) :
    (algebraMap (𝓞 F) (v.adicCompletionIntegers F) a) • y ∈ loc v (condIdeal S U • latE S) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    rw [← locVec_smul_int]
    exact locVec_mem_loc v (Submodule.smul_mem_smul ha hx)
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
  | smul c m _ hm => rw [smul_comm]; exact Submodule.smul_mem _ c hm

/-- **$\varpi^{c}\Lambda_\mathfrak p \subseteq (\mathfrak cL_E)_\mathfrak p$.** -/
theorem φ_mem_loc_condIdeal (hcU : ∀ v ∉ U, cv S v = 0) {v : HeightOneSpectrum (𝓞 F)} (w : Γ (locD S v))
    (h0 : πv v ^ (locD S v).c ∣ w.re) (h1 : πv v ^ (locD S v).c ∣ w.im) :
    φ (locD S v) w ∈ loc v (condIdeal S U • latE S) := by
  obtain ⟨a, ha, hav⟩ := exists_mem_condIdeal_valued hcU v
  set ia := algebraMap (𝓞 F) (v.adicCompletionIntegers F) a
  have hdvd : πv v ^ (locD S v).c ∣ ia := by
    rw [← Ideal.mem_span_singleton, NF.mem_span_π_pow]; exact hav.le
  obtain ⟨u, hu⟩ := hdvd
  have hπ0 : ((πv v ^ (locD S v).c : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 := by
    push_cast; exact pow_ne_zero _ (πF_ne_zero v)
  have hvu : Valued.v (u : v.adicCompletion F) = 1 := by
    have e1 : Valued.v ((ia : v.adicCompletion F)) = Valued.v ((πv v ^ (locD S v).c : v.adicCompletionIntegers F) :
        v.adicCompletion F) * Valued.v (u : v.adicCompletion F) := by rw [hu]; push_cast; rw [map_mul]
    have e2 : Valued.v ((πv v ^ (locD S v).c : v.adicCompletionIntegers F) : v.adicCompletion F) = exp (-((locD S v).c : ℤ)) := by
      push_cast; exact valued_πF_pow v (locD S v).c
    rw [show ((ia : v.adicCompletionIntegers F) : v.adicCompletion F) = algebraMap (𝓞 F) (v.adicCompletion F) a from rfl,
      hav, e2] at e1
    have hne : exp (-((locD S v).c : ℤ)) ≠ (0 : ℤᵐ⁰) := exp_ne_zero
    exact (mul_eq_left₀ hne).mp e1.symm
  have hu0 : (u : v.adicCompletion F) ≠ 0 := by intro h; rw [h, map_zero] at hvu; exact zero_ne_one hvu
  have hinv : Valued.v ((u : v.adicCompletion F)⁻¹) ≤ 1 := by rw [map_inv₀, hvu, inv_one]
  set ui : v.adicCompletionIntegers F := toO v _ hinv
  obtain ⟨r0, hr0⟩ := h0
  obtain ⟨r1, hr1⟩ := h1
  set z' : Γ (locD S v) := ui • (⟨r0, r1⟩ : Γ (locD S v))
  have hw : w = ia • z' := by
    refine QuadraticAlgebra.ext ?_ ?_
    · apply Subtype.ext
      simp only [z', QuadraticAlgebra.re_smul, smul_eq_mul, hr0, hu]
      push_cast
      simp only [ui, toO]
      field_simp
    · apply Subtype.ext
      simp only [z', QuadraticAlgebra.im_smul, smul_eq_mul, hr1, hu]
      push_cast
      simp only [ui, toO]
      field_simp
  rw [hw, φ_smul]
  exact smul_mem_loc_condIdeal ha (φ_mem (locD S v) z')

theorem condIdeal_ne_bot : condIdeal S U ≠ ⊥ := by
  rw [condIdeal, ← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
  intro v _
  exact pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact v.ne_bot)

/-- **The conductor of $\mathcal O_F[\theta]$ is $\mathfrak c\,\mathcal O_E$**, $\mathfrak c = \prod_{\mathfrak p\in U}\mathfrak p^{c_\mathfrak p}$ ($U$ containing every $\mathfrak p$ with
$c_\mathfrak p > 0$). *Proof:* $\supseteq$: $\mathfrak cL_E \subseteq \mathcal O_F^2$ (`smul_mem_intVec_of_mem_condIdeal`). $\subseteq$: an element of the
conductor lies in $\varpi^{c}\Lambda_\mathfrak p \subseteq (\mathfrak cL_E)_\mathfrak p$ at every $\mathfrak p$ (`exists_φ_of_conductor`, `φ_mem_loc_condIdeal`), hence in
$\mathfrak cL_E$ (`mem_iff_forall_loc`). -/
theorem conductor_eq_map (hcU : ∀ v ∉ U, cv S v = 0) :
    conductor (𝓞 F) (θO S) = (condIdeal S U).map (algebraMap (𝓞 F) (𝓞 E)) := by
  classical
  apply le_antisymm
  · intro y hy
    rw [mem_conductor_iff'] at hy
    set x := coordOf S (y : E) with hx
    have hcx : cE S x = y := cE_coordOf S _
    have hy' : ∀ x' ∈ latE S, mulMat S (cE S x) *ᵥ x' ∈ intVec := by rw [hcx]; exact hy
    obtain ⟨a0, ha0, ha0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (condIdeal_ne_bot (S := S) (U := U))
    have hD2 : (2 * D : 𝓞 F) ≠ 0 := mul_ne_zero two_ne_zero S.D_ne
    have hM : (condIdeal S U • latE S).IsLattice F :=
      isLattice_of_global_bounds (d := a0 * (2 * D)) (mul_ne_zero ha0ne hD2)
        (fun x' hx' => by
          rw [mul_smul]
          exact Submodule.smul_mem_smul ha0 (intVec_le_latE S (Submodule.smul_mem _ _ hx')))
        (fun x' hx' => by
          rw [mul_smul]
          exact Submodule.smul_mem _ _ (smul_mem_intVec_of_mem_latE S (Submodule.smul_le_right hx')))
    have hxM : x ∈ condIdeal S U • latE S := by
      rw [mem_iff_forall_loc hM]
      intro v
      obtain ⟨w, hw, h0, h1⟩ := exists_φ_of_conductor hy' (locD S v)
      rw [← hw]
      exact φ_mem_loc_condIdeal hcU w h0 h1
    have key : ∀ x' ∈ condIdeal S U • latE S,
        ∃ u ∈ (condIdeal S U).map (algebraMap (𝓞 F) (𝓞 E)), (u : E) = cE S x' := by
      intro x' hx'
      refine Submodule.smul_induction_on hx' (fun r hr n hn => ?_) (fun x1 x2 h1 h2 => ?_)
      · refine ⟨algebraMap (𝓞 F) (𝓞 E) r * ⟨cE S n, (mem_latE S).mp hn⟩,
          Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hr), ?_⟩
        show algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) r) * cE S n = cE S (r • n)
        rw [algebraMap_O_E, ← cE_smul, algebraMap_smul]
      · obtain ⟨u1, hu1, e1⟩ := h1
        obtain ⟨u2, hu2, e2⟩ := h2
        exact ⟨u1 + u2, Ideal.add_mem _ hu1 hu2, by
          rw [show ((u1 + u2 : 𝓞 E) : E) = u1 + u2 from rfl, e1, e2, cE_add]⟩
    obtain ⟨u, hu, hue⟩ := key x hxM
    have : u = y := RingOfIntegers.coe_injective (by
      show (u : E) = (y : E)
      rw [hue, hcx])
    rwa [← this]
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, mem_conductor_iff']
    intro x hx
    rw [show ((algebraMap (𝓞 F) (𝓞 E) a : 𝓞 E) : E) = algebraMap F E (algebraMap (𝓞 F) F a) from
      algebraMap_O_E a, mulMat_algebraMap_mulVec, algebraMap_smul]
    exact smul_mem_intVec_of_mem_condIdeal hcU ha hx

/-- **$N(\mathfrak f) = \bigl(\prod_{\mathfrak p\in U}N\mathfrak p^{c_\mathfrak p}\bigr)^2$.** -/
theorem absNorm_conductor (hcU : ∀ v ∉ U, cv S v = 0) :
    Ideal.absNorm (conductor (𝓞 F) (θO S)) = (∏ v ∈ U, Ideal.absNorm v.asIdeal ^ cv S v) ^ 2 := by
  rw [conductor_eq_map hcU, Ideal.absNorm_algebraMap, ← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E,
    Algebra.IsQuadraticExtension.finrank_eq_two, condIdeal, map_prod]
  simp only [map_pow]

/-- **The discriminant relation** $|d_E|\,\bigl(\prod_{\mathfrak p\in U}N\mathfrak p^{c_\mathfrak p}\bigr)^2 = 4^n|d_F|^2|N_{F/\mathbb Q}D|$ ($U \ni$ every
$\mathfrak p \mid 2D$). -/
@[kb "neukirch1999" "Ch. III §2, Prop. 2.4, Thm. 2.9 (discriminant of an order) [unverified]"]
theorem discr_relation (hU : ∀ v ∉ U, (2 * D : 𝓞 F) ∉ v.asIdeal) :
    |(discr E : ℝ)| * (∏ v ∈ U, (qv v : ℝ) ^ cv S v) ^ 2 =
      4 ^ Module.finrank ℚ F * |(discr F : ℝ)| ^ 2 * |(Algebra.norm ℚ (dF D) : ℝ)| := by
  have hcU : ∀ v ∉ U, cv S v = 0 := fun v hv => cv_eq_zero S (loc_latE_of_not_mem S v (hU v hv))
  rw [← discr_mul_absNorm_conductor S, absNorm_conductor hcU]
  push_cast
  rfl

end Global

end QuadFormsKB.Tamagawa.BinaryCM
