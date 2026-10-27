import QuadFormsKB.Tamagawa.BinaryCMLocalOrder

/-!
# Bridges: local stabilizers and local densities in terms of the quadratic order $\mathfrak o[\omega]$

**Layer:** as in `BinaryCMLocalOrder.lean`; `LocData` bundles the output of `exists_struct_loc`
($\Lambda = (\texttt{latE})_\mathfrak p = \varphi(\mathfrak o[\omega])$, $\omega^2 = a + b\omega$).

**Proves**
* `φ_mul`, `φ_norm`: $\varphi(z) = (z_0 + z_1s\tau^c, z_1\tau^c)$ is multiplicative (for the multiplication of $F_\mathfrak p[\sqrt{-d}]$ in
  coordinates) and carries the norm of $\mathfrak o[\omega]$ to $x_0^2 + dx_1^2$;
* **`relRatio_eq_ρc`**: the ratio $r = [O(\Lambda) : O(\mathfrak o^2)]$ of local stabilizers equals the norm-one index
  $\rho = [\Gamma^1 : (\mathfrak o + \varpi^c\Gamma)^1]$ (rotations by norm-one units, `Φ`; the reflection $\mathrm{diag}(1,-1)$ lies in both
  stabilizers, so the index is that of the proper parts, `relIndex_eq_relIndex_inf_so`);
* **`localDensity_eq_normOne`**: $\beta_\mathfrak p(\langle1,D\rangle, 1) = q^{-k}\#\{z \in (\mathfrak o + \varpi^c\Gamma)_k : N(z) = 1\}$ for large
  $k$ (the order $\mathfrak o[\sqrt{-d}] \cong \mathfrak o[\varpi^c\omega]$ by Mathlib's `changeGeneratorEquiv`).

-/

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.BinaryCM

open Lattices QuadForm QuadFormsKB.HilbertModular Binary.Rel BinaryNormOne Loc LocalDensity

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

variable {D : 𝓞 F} (S : SqrtData D E) (v : HeightOneSpectrum (𝓞 F))

local notation "QD" => formF (diagForm1 D)

/-- $\tau = \varpi^{-1}$. -/
abbrev τv : v.adicCompletion F := (πF v)⁻¹

theorem vec2_ext {R : Type*} {x y : Fin 2 → R} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  funext i; fin_cases i
  · exact h0
  · exact h1

theorem rotMat_mulVec_eq {R : Type*} [CommRing R] (d p q : R) (y : Fin 2 → R) :
    rotMat d p q 1 *ᵥ y = ![p * y 0 - d * q * y 1, q * y 0 + p * y 1] := by
  apply vec2_ext <;> simp [rotMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- **Local data of the maximal order** at $\mathfrak p$ (the output of `exists_struct_loc`). -/
structure LocData where
  c : ℕ
  s : v.adicCompletionIntegers F
  a : v.adicCompletionIntegers F
  b : v.adicCompletionIntegers F
  ha : πv v ^ (2 * c) * a = -(s ^ 2 + NF.ι v D)
  hb : πv v ^ c * b = 2 * s
  mem_iff : ∀ y : Fin 2 → v.adicCompletion F, y ∈ loc v (latE S) ↔ ∃ x t : v.adicCompletionIntegers F,
    y = omegaVec v c s x t

theorem nonempty_locData : Nonempty (LocData S v) := by
  obtain ⟨c, s, a, b, ha, hb, h⟩ := exists_struct_loc S v
  exact ⟨⟨c, s, a, b, ha, hb, h⟩⟩

variable {S v} (L : LocData S v)

theorem a_eq : ((L.a : v.adicCompletionIntegers F) : v.adicCompletion F) =
    -((L.s : v.adicCompletion F) ^ 2 + dIn D (v.adicCompletion F)) * τv v ^ (2 * L.c) := by
  have h := congrArg (fun z : v.adicCompletionIntegers F => (z : v.adicCompletion F)) L.ha
  push_cast at h
  rw [dIn_eq_ι, ← h, inv_pow]
  have := πF_ne_zero v
  field_simp

theorem b_eq : ((L.b : v.adicCompletionIntegers F) : v.adicCompletion F) =
    2 * (L.s : v.adicCompletion F) * τv v ^ L.c := by
  have h := congrArg (fun z : v.adicCompletionIntegers F => (z : v.adicCompletion F)) L.hb
  have h2 : ((2 : v.adicCompletionIntegers F) : v.adicCompletion F) = 2 := rfl
  have h' : (πF v) ^ L.c * (L.b : v.adicCompletion F) = 2 * (L.s : v.adicCompletion F) := by
    push_cast at h
    rw [h2] at h
    exact h
  have := πF_ne_zero v
  rw [inv_pow]
  field_simp
  linear_combination h'

/-- $\Gamma = \mathfrak o[\omega]$. -/
abbrev Γ := QuadraticAlgebra (v.adicCompletionIntegers F) L.a L.b

/-- **The coordinates of $z \in \Gamma$:** $\varphi(z) = z_0 + z_1\omega$, $\omega = (s\tau^c, \tau^c)$. -/
def φ (z : Γ L) : Fin 2 → v.adicCompletion F := omegaVec v L.c L.s z.re z.im

theorem φ_zero' (z : Γ L) : φ L z 0 = (z.re : v.adicCompletion F) + (z.im : v.adicCompletion F) *
    (L.s : v.adicCompletion F) * τv v ^ L.c := rfl

theorem φ_one' (z : Γ L) : φ L z 1 = (z.im : v.adicCompletion F) * τv v ^ L.c := rfl

theorem mem_loc_iff_φ (y : Fin 2 → v.adicCompletion F) : y ∈ loc v (latE S) ↔ ∃ z : Γ L, φ L z = y := by
  rw [L.mem_iff]
  constructor
  · rintro ⟨x, t, rfl⟩; exact ⟨⟨x, t⟩, rfl⟩
  · rintro ⟨z, rfl⟩; exact ⟨z.re, z.im, rfl⟩

theorem φ_mem (z : Γ L) : φ L z ∈ loc v (latE S) := (mem_loc_iff_φ L _).mpr ⟨z, rfl⟩

theorem rotMat_mul_rotMat' {R : Type*} [CommRing R] (d p q p' q' : R) :
    rotMat d p q 1 * rotMat d p' q' 1 = rotMat d (p * p' - d * q * q') (q * p' + p * q') 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **$\varphi$ is multiplicative:** $\varphi(zw) = \varphi(z)\cdot\varphi(w)$, the product of $F_\mathfrak p[\sqrt{-d}]$ in coordinates. -/
theorem φ_mul (z w : Γ L) :
    rotMat (dIn D (v.adicCompletion F)) (φ L z 0) (φ L z 1) 1 *ᵥ φ L w = φ L (z * w) := by
  have ha := a_eq L
  have hb := b_eq L
  rw [rotMat_mulVec_eq]
  apply vec2_ext
  · simp only [Matrix.cons_val_zero]
    rw [φ_zero', φ_zero', φ_one', φ_one', φ_zero', QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    push_cast
    rw [ha, hb]
    ring
  · simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [φ_zero', φ_zero', φ_one', φ_one', φ_one', QuadraticAlgebra.im_mul]
    push_cast
    rw [hb]
    ring

/-- **$\varphi$ carries the norm:** $\varphi(z)_0^2 + d\varphi(z)_1^2 = N(z)$. -/
theorem φ_norm (z : Γ L) :
    φ L z 0 ^ 2 + dIn D (v.adicCompletion F) * φ L z 1 ^ 2 =
      ((QuadraticAlgebra.norm z : v.adicCompletionIntegers F) : v.adicCompletion F) := by
  have ha := a_eq L
  have hb := b_eq L
  rw [φ_zero', φ_one', QuadraticAlgebra.norm_def]
  push_cast
  rw [ha, hb]
  ring

theorem φ_one : φ L 1 = ![1, 0] := by
  apply vec2_ext
  · rw [φ_zero', QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]; simp
  · rw [φ_one', QuadraticAlgebra.im_one]; simp

theorem φ_injective : Function.Injective (φ L) := by
  intro z w h
  have h1 := congrFun h 1
  have h0 := congrFun h 0
  rw [φ_one', φ_one'] at h1
  have hτ : τv v ^ L.c ≠ 0 := pow_ne_zero _ (inv_ne_zero (πF_ne_zero v))
  have him : (z.im : v.adicCompletion F) = w.im := mul_right_cancel₀ hτ h1
  rw [φ_zero', φ_zero', him] at h0
  have hre : (z.re : v.adicCompletion F) = w.re := by linear_combination h0
  exact QuadraticAlgebra.ext (Subtype.ext hre) (Subtype.ext him)

/-! ### Rotations by norm-one units of $\Gamma$ -/

theorem coe_norm_eq_one_iff (z : Γ L) :
    ((QuadraticAlgebra.norm z : v.adicCompletionIntegers F) : v.adicCompletion F) = 1 ↔
      QuadraticAlgebra.norm z = 1 := by
  constructor
  · intro h; exact Subtype.ext h
  · intro h; rw [h]; rfl

theorem mem_ker_normΓ_iff (u : (Γ L)ˣ) : u ∈ (normΓ v L.a L.b).ker ↔ QuadraticAlgebra.norm (u : Γ L) = 1 := by
  rw [MonoidHom.mem_ker, Units.ext_iff]; rfl

theorem φ_norm_one {u : Γ L} (hu : QuadraticAlgebra.norm u = 1) :
    φ L u 0 ^ 2 + dIn D (v.adicCompletion F) * φ L u 1 ^ 2 = 1 := by
  rw [φ_norm, (coe_norm_eq_one_iff L u).mpr hu]

/-- The rotation by a norm-one unit $u \in \Gamma^1$: multiplication by $\varphi(u)$. -/
def rotU (u : (normΓ v L.a L.b).ker) : GL (Fin 2) (v.adicCompletion F) :=
  rotGL D (φ_norm_one L ((mem_ker_normΓ_iff L u.1).mp u.2)) (one_pow 2)

theorem rotU_val (u : (normΓ v L.a L.b).ker) :
    (rotU L u).val = rotMat (dIn D (v.adicCompletion F)) (φ L (u.1 : Γ L) 0) (φ L (u.1 : Γ L) 1) 1 := rfl

theorem rotU_mulVec (u : (normΓ v L.a L.b).ker) (z : Γ L) :
    (rotU L u).val *ᵥ φ L z = φ L ((u.1 : Γ L) * z) := by rw [rotU_val, φ_mul]

/-- **$\Phi : \Gamma^1 \to SO(V)(F_\mathfrak p)$**, $u \mapsto$ multiplication by $\varphi(u)$, a group homomorphism. -/
def Φ : (normΓ v L.a L.b).ker →* orthGroup QD (v.adicCompletion F) where
  toFun u := ⟨rotU L u, rotGL_mem D _ _⟩
  map_one' := by
    apply Subtype.ext; apply Units.ext
    show rotMat _ (φ L 1 0) (φ L 1 1) 1 = 1
    rw [φ_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp [rotMat]
  map_mul' u w := by
    apply Subtype.ext; apply Units.ext
    show rotMat _ (φ L ((u.1 : Γ L) * w.1) 0) (φ L ((u.1 : Γ L) * w.1) 1) 1 =
      rotMat _ (φ L (u.1 : Γ L) 0) (φ L (u.1 : Γ L) 1) 1 * rotMat _ (φ L (w.1 : Γ L) 0) (φ L (w.1 : Γ L) 1) 1
    rw [rotMat_mul_rotMat', ← φ_mul, rotMat_mulVec_eq]
    rfl

theorem Φ_val (u : (normΓ v L.a L.b).ker) : (Φ L u).1 = rotU L u := rfl

theorem Φ_injective : Function.Injective (Φ L) := by
  intro u w h
  have h' := congrArg (fun g : orthGroup QD (v.adicCompletion F) => g.1.val) h
  simp only [Φ_val, rotU_val] at h'
  have h0 := congrFun (congrFun h' 0) 0
  have h1 := congrFun (congrFun h' 1) 0
  simp [rotMat] at h0 h1
  have hφ : φ L (u.1 : Γ L) = φ L (w.1 : Γ L) := vec2_ext h0 h1
  exact Subtype.ext (Units.ext (φ_injective L hφ))

theorem det_Φ (u : (normΓ v L.a L.b).ker) : (Φ L u).1.val.det = 1 :=
  det_rotMat (φ_norm_one L ((mem_ker_normΓ_iff L u.1).mp u.2))

theorem locAct_eq_of_le {g : GL (Fin 2) (v.adicCompletion F)}
    {M : Submodule (v.adicCompletionIntegers F) (Fin 2 → v.adicCompletion F)}
    (h1 : locAct v g M ≤ M) (h2 : locAct v g⁻¹ M ≤ M) : locAct v g M = M := by
  refine le_antisymm h1 ?_
  have := Submodule.map_mono (f := (Matrix.mulVecLin g.val).restrictScalars (v.adicCompletionIntegers F)) h2
  calc M = locAct v g (locAct v g⁻¹ M) := by rw [← locAct_mul, mul_inv_cancel, locAct_one]
    _ ≤ locAct v g M := this

theorem locAct_rotU_le (u : (normΓ v L.a L.b).ker) : locAct v (rotU L u) (loc v (latE S)) ≤ loc v (latE S) := by
  rintro y ⟨w, hw, rfl⟩
  obtain ⟨z, rfl⟩ := (mem_loc_iff_φ L w).mp hw
  show (rotU L u).val *ᵥ φ L z ∈ _
  rw [rotU_mulVec]; exact φ_mem L _

theorem rotU_inv (u : (normΓ v L.a L.b).ker) : (rotU L u)⁻¹ = rotU L u⁻¹ := by
  have : (Φ L u)⁻¹ = Φ L u⁻¹ := (map_inv (Φ L) u).symm
  exact congrArg (fun g : orthGroup QD (v.adicCompletion F) => g.1) this

theorem mem_stabLat_iff (g : orthGroup QD (v.adicCompletion F))
    (M : Submodule (v.adicCompletionIntegers F) (Fin 2 → v.adicCompletion F)) :
    g ∈ stabLat v (orthGroup QD (v.adicCompletion F)).subtype M ↔ locAct v g.1 M = M := Iff.rfl

theorem mem_soSub_iff' (g : orthGroup QD (v.adicCompletion F)) :
    g ∈ soSub QD (v.adicCompletion F) ↔ g.1.val.det = 1 := Iff.rfl

theorem mem_range_Φ_of {g : orthGroup QD (v.adicCompletion F)} (hdet : g.1.val.det = 1)
    (hy : g.1.val *ᵥ ![1, 0] ∈ loc v (latE S)) : g ∈ (Φ L).range := by
  obtain ⟨e1, -, e3, -⟩ := orth_diag D S.D_ne g.2
  obtain ⟨z, hz⟩ := (mem_loc_iff_φ L _).mp hy
  have hz0 : φ L z 0 = g.1.val 0 0 := by rw [hz]; simp [Matrix.mulVec, dotProduct]
  have hz1 : φ L z 1 = g.1.val 1 0 := by rw [hz]; simp [Matrix.mulVec, dotProduct]
  have hN : QuadraticAlgebra.norm z = 1 := by
    rw [← coe_norm_eq_one_iff, ← φ_norm, hz0, hz1]; exact e3
  have hzu : IsUnit z := QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (by rw [hN]; exact isUnit_one)
  refine ⟨⟨hzu.unit, (mem_ker_normΓ_iff L _).mpr hN⟩, ?_⟩
  apply Subtype.ext; apply Units.ext
  show rotMat _ (φ L z 0) (φ L z 1) 1 = _
  rw [hz0, hz1, ← hdet, ← e1]

/-- **The image of $\Phi$ is the proper stabilizer of $\Lambda$:** $\Phi(\Gamma^1) = O(\Lambda) \cap SO(V)(F_\mathfrak p)$. -/
theorem range_Φ : (Φ L).range =
    stabLat v (orthGroup QD (v.adicCompletion F)).subtype (loc v (latE S)) ⊓ soSub QD (v.adicCompletion F) := by
  ext g
  rw [Subgroup.mem_inf, mem_stabLat_iff, mem_soSub_iff']
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨?_, det_Φ L u⟩
    rw [Φ_val]
    have h1 := locAct_rotU_le L u
    have h2 := locAct_rotU_le L u⁻¹
    rw [← rotU_inv] at h2
    exact locAct_eq_of_le h1 h2
  · rintro ⟨hgΛ, hdet⟩
    refine mem_range_Φ_of L hdet ?_
    rw [← hgΛ]; exact ⟨_, mem_loc_of_mem_std S v (e0_mem_std v), rfl⟩

theorem mem_Hc_iff (z : (Γ L)ˣ) : z ∈ Hc v L.a L.b L.c ↔ πv v ^ L.c ∣ (z : Γ L).im := by
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s.val.im, ιc_im v L.a L.b L.c s.val⟩
  · rintro ⟨t, ht⟩
    set s : QuadraticAlgebra (v.adicCompletionIntegers F) (πv v ^ (2 * L.c) * L.a) (πv v ^ L.c * L.b) :=
      ⟨(z : Γ L).re, t⟩
    have hs : ιc v L.a L.b L.c s = z := QuadraticAlgebra.ext rfl ht.symm
    have hsu : IsUnit s := by
      rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, ← norm_ιc, hs, ← QuadraticAlgebra.isUnit_iff_norm_isUnit]
      exact z.isUnit
    exact ⟨hsu.unit, Units.ext (by rw [Units.coe_map, IsUnit.unit_spec]; exact hs)⟩

theorem φ_mem_std_iff (z : Γ L) : φ L z ∈ std v ↔ πv v ^ L.c ∣ z.im := by
  have hτ : τv v ^ L.c * πF v ^ L.c = 1 := by rw [inv_pow]; exact inv_mul_cancel₀ (pow_ne_zero _ (πF_ne_zero v))
  constructor
  · intro h
    have h1 := h 1
    rw [φ_one'] at h1
    rw [← Ideal.mem_span_singleton, NF.mem_span_π_pow]
    have : Valued.v ((z.im : v.adicCompletion F)) = Valued.v ((z.im : v.adicCompletion F) * τv v ^ L.c) *
        Valued.v (πF v ^ L.c) := by
      rw [← map_mul, mul_assoc, hτ, mul_one]
    rw [this, valued_πF_pow]
    calc Valued.v ((z.im : v.adicCompletion F) * τv v ^ L.c) * exp (-(L.c : ℤ)) ≤ 1 * exp (-(L.c : ℤ)) :=
          mul_le_mul_left (by simpa using h1) _
      _ = exp (-(L.c : ℤ)) := one_mul _
  · rintro ⟨t, ht⟩
    have him : (z.im : v.adicCompletion F) * τv v ^ L.c = t := by
      have := πF_ne_zero v
      rw [ht]; push_cast
      rw [inv_pow]
      field_simp
    intro i; fin_cases i
    · show Valued.v (φ L z 0) ≤ exp (-(0 : ℤ))
      rw [φ_zero', mul_assoc, mul_comm (L.s : v.adicCompletion F), ← mul_assoc, him]
      simp only [neg_zero, exp_zero]
      refine Valuation.map_add_le _ ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp z.re.2) ?_
      rw [map_mul]
      exact mul_le_one' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp t.2)
        ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp L.s.2)
    · show Valued.v (φ L z 1) ≤ exp (-(0 : ℤ))
      rw [φ_one', him]
      simpa using (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp t.2

/-- **$\Phi(u) \in O(\mathfrak o^2)$ iff $u \in (\mathfrak o + \varpi^c\Gamma)^\times$.** -/
theorem Φ_mem_stdStab_iff (u : (normΓ v L.a L.b).ker) :
    Φ L u ∈ stdStab QD v ↔ (u.1 : (Γ L)ˣ) ∈ Hc v L.a L.b L.c := by
  rw [mem_Hc_iff, ← φ_mem_std_iff]
  constructor
  · intro h
    have h' : locAct v (rotU L u) (std v) = std v := h
    have : (rotU L u).val *ᵥ ![1, 0] ∈ std v := by rw [← h']; exact ⟨_, e0_mem_std v, rfl⟩
    rwa [← φ_one L, rotU_mulVec, mul_one] at this
  · intro h
    show locAct v (rotU L u) (std v) = std v
    refine locAct_std_of_inv_mem D v S.D_ne (rotGL_mem D _ _) ?_
    show rotMatInv _ (φ L (u.1 : Γ L) 0) (φ L (u.1 : Γ L) 1) 1 *ᵥ ![1, 0] ∈ std v
    have e : rotMatInv (dIn D (v.adicCompletion F)) (φ L (u.1 : Γ L) 0) (φ L (u.1 : Γ L) 1) 1 *ᵥ ![1, 0] =
        ![φ L (u.1 : Γ L) 0, -(φ L (u.1 : Γ L) 1)] := by
      apply vec2_ext <;> simp [rotMatInv, Matrix.mulVec, dotProduct]
    rw [e]
    intro i; fin_cases i
    · exact h 0
    · show Valued.v (-(φ L (u.1 : Γ L) 1)) ≤ _
      rw [Valuation.map_neg]; exact h 1

/-! ### The reflection $\mathrm{diag}(1,-1)$ and the ratio of stabilizers -/

theorem nondeg_QD (hD : D ≠ 0) : (formF (diagForm1 D)).Nondegenerate := by
  rw [QuadForm.Nondegenerate]
  have : (formF (diagForm1 D)).hessian = (diagForm1 D).hessian.map (algebraMap (𝓞 F) F) := by
    ext i j; simp [QuadForm.hessian, QuadForm.map]
  rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hessian_det_diagForm1]
  exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr (mul_ne_zero (by norm_num) hD)

variable (D v) in
/-- $\sigma_\mathfrak p = \mathrm{diag}(1,-1) = \mathrm{rotMat}(d,1,0,-1)$, an improper isometry. -/
def σv : orthGroup (formF (diagForm1 D)) (v.adicCompletion F) :=
  ⟨rotGL D (K := v.adicCompletion F) (a := 1) (b := 0) (s := -1) (by simp) (by norm_num), rotGL_mem D _ _⟩

theorem σv_val : (σv D v).1.val = rotMat (dIn D (v.adicCompletion F)) 1 0 (-1) := rfl

theorem det_σv : (σv D v).1.val.det = -1 := det_rotMat (by simp)

include S in
theorem σv_mem_stdStab : σv D v ∈ stdStab QD v := by
  show locAct v (σv D v).1 (std v) = std v
  refine locAct_std_of_inv_mem D v S.D_ne (σv D v).2 ?_
  show rotMatInv _ 1 0 (-1) *ᵥ ![1, 0] ∈ std v
  have e : rotMatInv (dIn D (v.adicCompletion F)) (1 : v.adicCompletion F) 0 (-1) *ᵥ ![1, 0] = ![1, 0] := by
    apply vec2_ext <;> simp [rotMatInv, Matrix.mulVec, dotProduct]
  rw [e]; exact e0_mem_std v

theorem σv_mulVec_φ (z : Γ L) : (σv D v).1.val *ᵥ φ L z = φ L (star z) := by
  have hb := b_eq L
  have e : rotMat (dIn D (v.adicCompletion F)) 1 0 (-1) *ᵥ φ L z = ![φ L z 0, -(φ L z 1)] := by
    apply vec2_ext <;> simp [rotMat, Matrix.mulVec, dotProduct]
  rw [σv_val, e]
  apply vec2_ext
  · simp only [Matrix.cons_val_zero]
    rw [φ_zero', φ_zero', QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
    push_cast
    rw [hb]; ring
  · simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [φ_one', φ_one', QuadraticAlgebra.im_star]
    push_cast; ring

include L in
theorem σv_mem_stabΛ :
    σv D v ∈ stabLat v (orthGroup QD (v.adicCompletion F)).subtype (loc v (latE S)) := by
  rw [mem_stabLat_iff]
  have hle : ∀ g : orthGroup QD (v.adicCompletion F), g.1.val = rotMat (dIn D (v.adicCompletion F)) 1 0 (-1) →
      locAct v g.1 (loc v (latE S)) ≤ loc v (latE S) := by
    intro g hg
    rintro y ⟨w, hw, rfl⟩
    obtain ⟨z, rfl⟩ := (mem_loc_iff_φ L w).mp hw
    show g.1.val *ᵥ φ L z ∈ _
    rw [hg, ← σv_val, σv_mulVec_φ L]
    exact φ_mem L _
  refine locAct_eq_of_le (hle _ rfl) ?_
  have hinv : (σv D v).1⁻¹ = (σv D v).1 := by
    apply Units.ext
    show rotMatInv _ 1 0 (-1) = rotMat _ 1 0 (-1)
    ext i j; fin_cases i <;> fin_cases j <;> simp [rotMat, rotMatInv]
  rw [hinv]; exact hle _ rfl

/-- $[A : A \cap SO] = 2$ for a subgroup $A$ of $O(V)(F_\mathfrak p)$ containing an improper isometry. -/
theorem relIndex_soSub_eq_two (hD : D ≠ 0) {A : Subgroup (orthGroup QD (v.adicCompletion F))}
    {σ : orthGroup QD (v.adicCompletion F)} (hσ : σ ∈ A) (hσdet : σ.1.val.det = -1) :
    (soSub QD (v.adicCompletion F)).relIndex A = 2 := by
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨σ, hσ⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  rw [mem_soSub_iff', mem_soSub_iff', Subgroup.coe_mul, Units.val_mul, det_mul, hσdet]
  rcases det_eq_one_or_neg_one QD (nondeg_QD hD) b.1 with h | h <;> rw [h] <;> norm_num

/-- **Indices of stabilizers containing $\mathrm{diag}(1,-1)$ are indices of their proper parts.** -/
theorem relIndex_eq_relIndex_inf_so (hD : D ≠ 0) {A B : Subgroup (orthGroup QD (v.adicCompletion F))} (hBA : B ≤ A)
    {σ : orthGroup QD (v.adicCompletion F)} (hσ : σ ∈ B) (hσdet : σ.1.val.det = -1) :
    B.relIndex A = (B ⊓ soSub QD (v.adicCompletion F)).relIndex (A ⊓ soSub QD (v.adicCompletion F)) := by
  set N := soSub QD (v.adicCompletion F)
  have h1 := Subgroup.relIndex_inf_mul_relIndex B N A
  have h2 := Subgroup.relIndex_mul_relIndex (B ⊓ N) B A inf_le_left hBA
  have hA : N.relIndex A = 2 := relIndex_soSub_eq_two hD (hBA hσ) hσdet
  have hB : (B ⊓ N).relIndex B = 2 := by
    rw [Subgroup.inf_relIndex_left]; exact relIndex_soSub_eq_two hD hσ hσdet
  rw [hA] at h1
  rw [hB, ← h1] at h2
  have h3 : B.relIndex A = B.relIndex (N ⊓ A) := by omega
  rw [h3, ← Subgroup.inf_relIndex_right B (N ⊓ A), ← Subgroup.inf_relIndex_right (B ⊓ N) (A ⊓ N)]
  congr 1
  · ext g; simp only [Subgroup.mem_inf]; tauto
  · rw [inf_comm]

/-- **The local ratio for $\Lambda = (\mathcal O_E)_\mathfrak p$ is the norm-one index** $\rho = [\Gamma^1 : (\mathfrak o + \varpi^c\Gamma)^1]$:
$r(O(\Lambda), O(\mathfrak o^2)) = [O(\Lambda) : O(\mathfrak o^2)] = [O(\Lambda)\cap SO : O(\mathfrak o^2) \cap SO] = \rho$. -/
theorem relRatio_eq_ρc :
    relRatio (stabLat v (orthGroup QD (v.adicCompletion F)).subtype (loc v (latE S))) (stdStab QD v) =
      ρc v L.a L.b L.c := by
  set A := stabLat v (orthGroup QD (v.adicCompletion F)).subtype (loc v (latE S))
  set B := stdStab QD v
  set N := soSub QD (v.adicCompletion F)
  -- the proper part of B lies in the image of Φ
  have hBN : ∀ g ∈ B, g ∈ N → g ∈ (Φ L).range := by
    intro g hg hgN
    refine mem_range_Φ_of L hgN ?_
    have hg' : locAct v g.1 (std v) = std v := hg
    have : g.1.val *ᵥ ![1, 0] ∈ std v := by rw [← hg']; exact ⟨_, e0_mem_std v, rfl⟩
    exact mem_loc_of_mem_std S v this
  have hBA : B ≤ A := by
    intro g hg
    rcases det_eq_one_or_neg_one QD (nondeg_QD S.D_ne) g with hdet | hdet
    · have := hBN g hg hdet
      rw [range_Φ L] at this
      exact this.1
    · have hσg : (σv D v)⁻¹ * g ∈ N := by
        rw [mem_soSub_iff', Subgroup.coe_mul, Units.val_mul, det_mul, hdet]
        have hi := congrArg Matrix.det (Units.inv_mul (σv D v).1)
        rw [det_mul, det_σv, det_one] at hi
        rw [Subgroup.coe_inv]
        linear_combination hi
      have hσgB : (σv D v)⁻¹ * g ∈ B := B.mul_mem (B.inv_mem (σv_mem_stdStab (S := S))) hg
      have h1 := hBN _ hσgB hσg
      rw [range_Φ L] at h1
      have := A.mul_mem (σv_mem_stabΛ L) h1.1
      rwa [mul_inv_cancel_left] at this
  rw [relRatio, Subgroup.relIndex_eq_one.mpr hBA, Nat.cast_one, div_one]
  rw [relIndex_eq_relIndex_inf_so S.D_ne hBA (σv_mem_stdStab (S := S)) det_σv]
  set Hc' := (Hc v L.a L.b L.c).subgroupOf (normΓ v L.a L.b).ker
  have hAN : A ⊓ N = (⊤ : Subgroup (normΓ v L.a L.b).ker).map (Φ L) := by
    rw [← MonoidHom.range_eq_map, range_Φ L]
  have hBN' : B ⊓ N = Hc'.map (Φ L) := by
    ext g
    constructor
    · rintro ⟨hgB, hgN⟩
      obtain ⟨u, rfl⟩ := hBN g hgB hgN
      exact ⟨u, Subgroup.mem_subgroupOf.mpr ((Φ_mem_stdStab_iff L u).mp hgB), rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨(Φ_mem_stdStab_iff L u).mpr (Subgroup.mem_subgroupOf.mp hu), det_Φ L u⟩
  rw [hAN, hBN', Subgroup.relIndex_map_map_of_injective _ _ (Φ_injective L), Subgroup.relIndex_top_right]
  rfl

/-! ### The local density of $\langle 1, D\rangle$ at $1$ -/

theorem evalIn_Qp_diag (k : ℕ) (x : Fin 2 → Ok v k) :
    (NF.Qp v (diagForm1 D)).evalIn (Ok v k) x =
      x 0 ^ 2 + Ideal.Quotient.mk (Ideal.span {πv v ^ k}) (NF.ι v D) * x 1 ^ 2 := by
  simp [QuadForm.evalIn, NF.Qp, QuadForm.map, diagForm1, QuadForm.diag, Matrix.diagonal, Fin.sum_univ_two,
    Algebra.algebraMap_self]
  ring

/-- **The representation count of $1$ by $\langle1,D\rangle$ modulo $\varpi^k$ is the norm-one count of the suborder**
$\mathfrak o[\varpi^c\omega] \cong \mathfrak o[\sqrt{-d}]$ (change of generator $\varpi^c\omega = s + \sqrt{-d}$, Mathlib's `changeGeneratorEquiv`). -/
theorem repCount_eq_normOne (k : ℕ) :
    DVR.repCount (NF.Qp v (diagForm1 D)) (NF.π v) k (NF.ι v 1) =
      Nat.card {z : QAk v (πv v ^ (2 * L.c) * L.a) (πv v ^ L.c * L.b) k // QuadraticAlgebra.norm z = 1} := by
  set mk := Ideal.Quotient.mk (Ideal.span {πv v ^ k})
  have ha : mk (πv v ^ (2 * L.c) * L.a) = (1 : Ok v k) ^ 2 * mk (-(NF.ι v D)) - 1 * mk 0 * mk L.s - mk L.s ^ 2 := by
    rw [L.ha]; simp only [map_neg, map_add, map_pow, map_zero]; ring
  have hb : mk (πv v ^ L.c * L.b) = (1 : Ok v k) * mk 0 + 2 * mk L.s := by
    rw [L.hb]; simp only [map_mul, map_ofNat, map_zero]; ring
  let e := QuadraticAlgebra.changeGeneratorEquiv (mk (-(NF.ι v D))) (mk 0) (1 : (Ok v k)ˣ) (mk L.s) ha hb
  have h1 : mk (NF.ι v 1) = 1 := by rw [map_one, map_one]
  -- vectors ↔ the quadratic algebra with ω² = -d
  have e1 : {x : Fin 2 → Ok v k // (NF.Qp v (diagForm1 D)).evalIn (Ok v k) x = mk (NF.ι v 1)} ≃
      {w : QuadraticAlgebra (Ok v k) (mk (-(NF.ι v D))) (mk 0) // QuadraticAlgebra.norm w = 1} :=
    { toFun := fun x => ⟨⟨x.1 0, x.1 1⟩, by
        have := x.2
        rw [evalIn_Qp_diag] at this
        rw [QuadraticAlgebra.norm_def]
        simp only [map_neg, map_zero, zero_mul, add_zero]
        linear_combination this + h1⟩
      invFun := fun w => ⟨![w.1.re, w.1.im], by
        have := w.2
        rw [QuadraticAlgebra.norm_def] at this
        simp only [map_neg, map_zero, zero_mul, add_zero] at this
        rw [evalIn_Qp_diag]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        linear_combination this - h1⟩
      left_inv := fun x => by apply Subtype.ext; exact vec2_ext rfl rfl
      right_inv := fun w => rfl }
  rw [DVR.repCount]
  rw [Nat.card_congr e1]
  refine Nat.card_congr (Equiv.subtypeEquiv e.symm.toEquiv fun w => ?_)
  have key : QuadraticAlgebra.norm (e.symm w) = QuadraticAlgebra.norm w := by
    have := QuadraticAlgebra.norm_algHom e.toAlgHom e.injective (e.symm w)
    simpa using this.symm
  show _ ↔ QuadraticAlgebra.norm (e.symm w) = 1
  rw [key]

/-- **$\beta_\mathfrak p(\langle1,D\rangle, 1)$ in terms of the suborder:** for $k > v(4)$ large,
$\beta_\mathfrak p = q^{-k}\#\{z \in (\mathfrak o + \varpi^c\Gamma)_k : N(z) = 1\}$. -/
theorem localDensity_eq_normOne {e : ℕ}
    (he : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) 4) = WithZero.exp (-(e : ℤ))) :
    NF.localDensity v (diagForm1 D) 1 =
      (Nat.card {z : QAk v (πv v ^ (2 * L.c) * L.a) (πv v ^ L.c * L.b) (e + 1) //
          QuadraticAlgebra.norm z = 1} : ℝ) / (qv v : ℝ) ^ (e + 1) := by
  have hQ : (diagForm1 D).Nondegenerate := by
    rw [QuadForm.Nondegenerate, hessian_det_diagForm1]; exact mul_ne_zero (by norm_num) S.D_ne
  have hev := NF.localDensity_eventually_eq v (diagForm1 D) hQ 1 one_ne_zero
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hev
  set k := max K (e + 1)
  have hk := hK k (le_max_left _ _)
  rw [← hk, NF.repCount_eq_completion, repCount_eq_normOne L k]
  simp only [Nat.reduceSub, mul_one]
  rw [normOne_div_pow v _ _ he (le_max_right _ _), normOne_div_pow v _ _ he le_rfl]

/-- **The local factor at $\mathfrak p$** (every prime, dyadic included):
$$r_\mathfrak p\cdot\beta_\mathfrak p(\langle1,D\rangle, 1) = q^c\,\frac{|\Gamma_1^\times|\,j(\Gamma)}{q(q-1)},\qquad \Gamma = (\mathcal O_E)_\mathfrak p = \mathfrak o[\omega],$$
$r_\mathfrak p = r(O(\Lambda), O(\mathfrak o^2))$ (the ratio), $q^c = [\Lambda : \mathfrak o^2]$. -/
theorem relRatio_mul_localDensity :
    relRatio (stabLat v (orthGroup QD (v.adicCompletion F)).subtype (loc v (latE S))) (stdStab QD v) *
        NF.localDensity v (diagForm1 D) 1 =
      (qv v : ℝ) ^ L.c * (Nat.card (QAk v L.a L.b 1)ˣ * jΓ v L.a L.b / (qv v * (qv v - 1))) := by
  obtain ⟨e, he⟩ := exists_valued_four v
  rw [relRatio_eq_ρc L, localDensity_eq_normOne L he]
  exact rho_mul_normOne_div_pow_all v L.a L.b L.c he le_rfl

end QuadFormsKB.Tamagawa.BinaryCM
