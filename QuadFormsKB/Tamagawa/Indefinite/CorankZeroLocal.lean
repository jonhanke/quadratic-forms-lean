/-
# Local counts for frames of corank zero

**Layer:** number fields, completions at finite primes (dyadic included). $F$ a number field, $Q_0$ nondegenerate over
$\mathcal O_F$ in $N$ variables, $T_0$ nondegenerate over $\mathcal O_F$ in the same number $N$ of variables, $\Xi$ a rational
frame of $T_0$ ($Q_0\circ\Xi = T_0$, so $\Xi\in\mathrm{GL}_N(F)$ is an isometry $(F^N, T_0)\to(F^N, Q_0)$). The complement of the
frame is $0$-dimensional ($n' = N - r = 0$), so the adapted frame of the frame route is $g = \Xi$ itself with the
form $Q'$ in zero variables (`adaptedZero`); no `FrameTower` is needed.

**Proves**
* `locCountZero` $n_v$, the number of $SO(L_v)$-orbits of integral frames of $T_0$ at $v$ in the $SO(Q_0)(F_v)$-orbit of
  $\Xi$ ("proper" integral frames); **`locCountZero_mul_aSO`**, the local identity for corank zero:
  $$n_v\,\mu_v(SO(L_v)) = \tfrac12\,\beta_v(L,T_0)\,|\det\Xi|_v.$$
  From `frameLocalIdentityGen` with $n' = 0$ (no hypothesis on $n'$ there): the weights are $1$ (the group $O(Q')$ is
  trivial), $\beta_v(Q',Q') = 1$ in zero variables, and $\mu_v(SO(L_v)) = \tfrac12\beta_v(L,L)$ (`aSO_eq_siegelDensity`). The
  $\tfrac12$ is $[O(L_v):SO(L_v)]^{-1}$: here it is not cancelled by an improper automorph of the complement, which is
  $0$-dimensional (this is why `locOrbitSum_eq` needs $n'\ge1$);
* `locCountZero_eq_one`: $n_v = 1$ outside the finite set `badZero`;
* **`tsum_one_finOrbit_zero`**: the number of $SO(\hat L)$-orbits of integral finite-adelic frames in $SO(V)(\mathbb A_f)\,\Xi_f$
  is $\prod_vn_v$ (a finite product), the analogue of `finOrbitMap_bijective` with the adapted frame `adaptedZero`.
Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.Indefinite.SiegelCorankOne

open MeasureTheory Set Matrix MulAction
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Frames LocalDensity

variable {F : Type} [Field F] [NumberField F]

/-! ### The form in zero variables -/

/-- **The quadratic form in zero variables** (the complement of a frame of corank zero). -/
def formZero (A : Type*) [CommRing A] : QuadForm A 0 := ⟨0, fun i => i.elim0⟩

/-- $T\perp Q' = T$ when $Q'$ has zero variables. -/
theorem blockForm_zero {A : Type*} [CommRing A] {N : ℕ} (T : QuadForm A N) (Q' : QuadForm A 0) :
    blockForm T Q' = T := by
  ext i j
  obtain ⟨i, rfl⟩ : ∃ i' : Fin N, Fin.castAdd 0 i' = i := ⟨i, rfl⟩
  obtain ⟨j, rfl⟩ : ∃ j' : Fin N, Fin.castAdd 0 j' = j := ⟨j, rfl⟩
  exact blockMat_castAdd_castAdd _ _ _ _ i j

/-- The form in zero variables is nondegenerate (the determinant of the empty matrix is $1$). -/
theorem formZero_nondegenerate : (formZero (𝓞 F)).Nondegenerate := by
  show (formZero (𝓞 F)).hessian.det ≠ 0
  rw [Matrix.det_isEmpty]; exact one_ne_zero

/-- $\beta_v(Q', Q') = 1$ for the form in zero variables. -/
theorem localDensityForm_formZero (v : HeightOneSpectrum (𝓞 F)) :
    NF.localDensityForm v (formZero (𝓞 F)) (formZero (𝓞 F)) = 1 := by
  unfold NF.localDensityForm
  have : (fun k : ℕ => (NF.repCountForm v (formZero (𝓞 F)) (formZero (𝓞 F)) k : ℝ) /
      (Ideal.absNorm v.asIdeal : ℝ) ^ (k * (0 * 0 - 0 * (0 + 1) / 2))) = fun _ => 1 := by
    funext k
    have h1 : NF.repCountForm v (formZero (𝓞 F)) (formZero (𝓞 F)) k = 1 := by
      unfold NF.repCountForm
      have e : ∀ X Y : Matrix (Fin 0) (Fin 0) (𝓞 F ⧸ v.asIdeal ^ k), X = Y := fun X Y =>
        Matrix.ext fun i => i.elim0
      have e' : ∀ X Y : QuadForm (𝓞 F ⧸ v.asIdeal ^ k) 0, X = Y := fun X Y =>
        QuadForm.ext (Matrix.ext fun i => i.elim0)
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext (e _ _)⟩, ⟨⟨fun _ _ => 0, e' _ _⟩⟩⟩
    simp [h1]
  rw [this]
  exact (tendsto_const_nhds).limUnder_eq

/-! ### The adapted frame of a frame of corank zero -/

section Adapted

variable {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) N) (hT : T₀.Nondegenerate) (Ξ : RatFrame Q₀ T₀)

include hT in
/-- A rational frame of corank zero is invertible: $\det\Xi\ne0$. -/
theorem det_ratFrame_ne_zero : Ξ.1.det ≠ 0 := by
  intro h0
  have hG : Ξ.1ᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian * Ξ.1 = (T₀.map (algebraMap (𝓞 F) F)).hessian := by
    rw [← QuadForm.hessian_compMat, Ξ.2]
  have := congrArg Matrix.det hG
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0] at this
  exact det_hessian_map_ne_zero T₀ hT (by rw [← this]; ring)

/-- **The adapted frame of corank zero**: $g = \Xi$, $Q' = $ the form in zero variables, $Q_0\circ\Xi = T_0 = T_0\perp Q'$. -/
def adaptedZero : AdaptedFrameT (r := N) (n' := 0) (Q₀.map (algebraMap (𝓞 F) F)) (T₀.map (algebraMap (𝓞 F) F)) where
  g := Matrix.nonsingInvUnit Ξ.1 (isUnit_iff_ne_zero.mpr (det_ratFrame_ne_zero Q₀ T₀ hT Ξ))
  Q' := formZero (𝓞 F)
  compMat_eq := by rw [blockForm_zero]; exact Ξ.2

theorem adaptedZero_g_val : (adaptedZero Q₀ T₀ hT Ξ).g.val = Ξ.1 := rfl

/-- The base frame $g E$ of the adapted frame at $v$ is $\Xi$. -/
theorem locBase_adaptedZero (v : HeightOneSpectrum (𝓞 F)) :
    locBase (r := N) (n' := 0) v Q₀ T₀ (adaptedZero Q₀ T₀ hT Ξ) = Ξ.1.map (σV v) := by
  show (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) (adaptedZero Q₀ T₀ hT Ξ).g).val *
    (stdFrameMat : Matrix (Fin (N + 0)) (Fin N) (v.adicCompletion F)) = _
  have : (stdFrameMat : Matrix (Fin (N + 0)) (Fin N) (v.adicCompletion F)) = 1 := by
    ext i j
    simp [stdFrameMat, Matrix.one_apply, Fin.ext_iff]
  rw [this, Matrix.mul_one]
  rfl

end Adapted

/-! ### Trivial groups in zero variables -/

section TrivialGroups

theorem subsingleton_GL_zero (R : Type*) [CommRing R] : Subsingleton (GL (Fin 0) R) :=
  ⟨fun _ _ => Units.ext (Matrix.ext fun i => i.elim0)⟩

/-- Over a trivial group the orbit quotient is the set itself. -/
theorem quotMk_bijective (G X : Type*) [Group G] [Subsingleton G] [MulAction G X] :
    Function.Bijective (Quotient.mk'' : X → orbitRel.Quotient G X) := by
  refine ⟨fun x y h => ?_, fun q => Quotient.inductionOn' q fun x => ⟨x, rfl⟩⟩
  obtain ⟨a, ha⟩ := orbitRel_apply.mp (Quotient.exact' h)
  obtain rfl : a = 1 := Subsingleton.elim a 1
  simpa using ha.symm

end TrivialGroups

/-! ### The local identity -/

section Local

variable {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) N) (hT : T₀.Nondegenerate)
  (Ξ : RatFrame Q₀ T₀)

/-- **The number $n_v$ of local orbits**: the $SO(L_v)$-orbits of integral frames of $T_0$ at $v$ in the
$SO(Q_0)(F_v)$-orbit of $\Xi$. -/
def locCountZero (v : HeightOneSpectrum (𝓞 F)) : ℕ :=
  Nat.card (LocOrbit (r := N) (n' := 0) v Q₀ T₀ (adaptedZero Q₀ T₀ hT Ξ))

include hQ in
/-- There are finitely many local orbits. -/
theorem finite_locOrbit_zero (hN : 0 < N) (v : HeightOneSpectrum (𝓞 F)) :
    Finite (LocOrbit (r := N) (n' := 0) v Q₀ T₀ (adaptedZero Q₀ T₀ hT Ξ)) := by
  have := subsingleton_GL_zero (v.adicCompletion F)
  have hb := ThQ_bijective (r := N) (n' := 0) v Q₀ T₀ (adaptedZero Q₀ T₀ hT Ξ) hQ hT (by omega : 0 < N + 0)
  have hf := finite_types (r := N) (n' := 0) v Q₀ T₀ (adaptedZero Q₀ T₀ hT Ξ) hQ hT
  have hbO := quotMk_bijective (orthGroup (((adaptedZero Q₀ T₀ hT Ξ).Q').map (algebraMap (𝓞 F) F)) (v.adicCompletion F))
    (LocFrameSetG v (T₀.map (algebraMap (𝓞 F) F)) (((adaptedZero Q₀ T₀ hT Ξ).Q').map (algebraMap (𝓞 F) F))
      (locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) (adaptedZero Q₀ T₀ hT Ξ).g)⁻¹ (std v)))
  have hX := Finite.of_injective _ hbO.1
  have hS := Finite.of_surjective _ (quotMk_bijective (soSub (((adaptedZero Q₀ T₀ hT Ξ).Q').map (algebraMap (𝓞 F) F)) (v.adicCompletion F))
    (LocFrameSetG v (T₀.map (algebraMap (𝓞 F) F)) (((adaptedZero Q₀ T₀ hT Ξ).Q').map (algebraMap (𝓞 F) F))
      (locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) (adaptedZero Q₀ T₀ hT Ξ).g)⁻¹ (std v)))).2
  exact Finite.of_injective _ hb.1

include hQ hT in
theorem locCount_mul_aSO_aux (hN : 0 < N) (v : HeightOneSpectrum (𝓞 F))
    (fr : AdaptedFrameT (r := N) (n' := 0) (Q₀.map (algebraMap (𝓞 F) F)) (T₀.map (algebraMap (𝓞 F) F)))
    (hQ0 : fr.Q' = formZero (𝓞 F)) :
    (Nat.card (LocOrbit (r := N) (n' := 0) v Q₀ T₀ fr) : ℝ) * aSO Q₀ v =
      2⁻¹ * NF.localDensityForm v Q₀ T₀ * ‖σV v fr.g.val.det‖ := by
  classical
  have := subsingleton_GL_zero (v.adicCompletion F)
  have hid := frameLocalIdentityGen (r := N) (n' := 0) v Q₀ hQ T₀ hT fr
  have hb := ThQ_bijective (r := N) (n' := 0) v Q₀ T₀ fr hQ hT (by omega : 0 < N + 0)
  have hbO := quotMk_bijective (orthGroup ((fr.Q').map (algebraMap (𝓞 F) F)) (v.adicCompletion F))
    (LocFrameSetG v (T₀.map (algebraMap (𝓞 F) F)) ((fr.Q').map (algebraMap (𝓞 F) F))
      (locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) fr.g)⁻¹ (std v)))
  have hbS := quotMk_bijective (soSub ((fr.Q').map (algebraMap (𝓞 F) F)) (v.adicCompletion F))
    (LocFrameSetG v (T₀.map (algebraMap (𝓞 F) F)) ((fr.Q').map (algebraMap (𝓞 F) F))
      (locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) fr.g)⁻¹ (std v)))
  have hf := finite_types (r := N) (n' := 0) v Q₀ T₀ fr hQ hT
  have hcard : Nat.card (LocOrbit (r := N) (n' := 0) v Q₀ T₀ fr) = Nat.card (LocFrameTypesG v (T₀.map (algebraMap (𝓞 F) F))
      ((fr.Q').map (algebraMap (𝓞 F) F))
      (locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) fr.g)⁻¹ (std v))) :=
    Nat.card_congr (((Equiv.ofBijective _ hb).trans (Equiv.ofBijective _ hbS).symm).trans (Equiv.ofBijective _ hbO))
  have hW : locFrameTypeSumG v (T₀.map (algebraMap (𝓞 F) F)) ((fr.Q').map (algebraMap (𝓞 F) F))
      (locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) fr.g)⁻¹ (std v)) =
      (Nat.card (LocFrameTypesG v (T₀.map (algebraMap (𝓞 F) F)) ((fr.Q').map (algebraMap (𝓞 F) F))
      (locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) fr.g)⁻¹ (std v))) : ℝ) := by
    have hw : ∀ M, locFrameWeightG v (T₀.map (algebraMap (𝓞 F) F)) ((fr.Q').map (algebraMap (𝓞 F) F))
        (locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) fr.g)⁻¹ (std v)) M = 1 := by
      intro M
      have : stabilizer (orthGroup ((fr.Q').map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) M =
          stdStab ((fr.Q').map (algebraMap (𝓞 F) F)) v :=
        Subgroup.ext fun g => by
          rw [Subsingleton.elim g 1]; exact ⟨fun _ => one_mem _, fun _ => one_mem _⟩
      unfold locFrameWeightG
      rw [this, Subgroup.relIndex_self]; norm_num
    unfold locFrameTypeSumG
    simp_rw [hw]
    have := Fintype.ofFinite (LocFrameTypesG v (T₀.map (algebraMap (𝓞 F) F)) ((fr.Q').map (algebraMap (𝓞 F) F))
      (locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) fr.g)⁻¹ (std v)))
    rw [finsum_eq_sum_of_fintype, Finset.sum_const, Nat.card_eq_fintype_card]
    simp
  have hβ : NF.localDensityForm v fr.Q' fr.Q' = 1 := by rw [hQ0]; exact localDensityForm_formZero v
  rw [hcard, ← hW, aSO_eq_siegelDensity Q₀ hQ v]
  simp only [NF.siegelDensity, ite_true]
  rw [hβ] at hid
  simp only [pow_zero, mul_one, zero_add, pow_one, one_mul] at hid
  rw [show ((1 / 2 : ℝ)) = 2⁻¹ by norm_num]
  have h2 : ‖algebraMap F (v.adicCompletion F) (fr.g.val.det)‖ = ‖σV v fr.g.val.det‖ := rfl
  rw [h2] at hid
  linear_combination 2⁻¹ * hid

include hQ in
/-- **The local identity for frames of corank zero** (every finite prime, dyadic included):
$$n_v\,\mu_v(SO(L_v)) = \tfrac12\,\beta_v(L,T_0)\,|\det\Xi|_v.$$ -/
theorem locCountZero_mul_aSO (hN : 0 < N) (v : HeightOneSpectrum (𝓞 F)) :
    (locCountZero Q₀ T₀ hT Ξ v : ℝ) * aSO Q₀ v = 2⁻¹ * NF.localDensityForm v Q₀ T₀ * ‖σV v Ξ.1.det‖ := by
  have := locCount_mul_aSO_aux Q₀ hQ T₀ hT hN v (adaptedZero Q₀ T₀ hT Ξ) rfl
  rwa [adaptedZero_g_val] at this

end Local

/-! ### The good places and the count of adelic orbits -/

section Global

variable {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) N) (hT : T₀.Nondegenerate)
  (Ξ : RatFrame Q₀ T₀)

/-- **The exceptional places** for corank zero: those of `frameBadSetG` for the lattice $\Xi^{-1}\mathcal O_F^N$. -/
def badZero : Finset (HeightOneSpectrum (𝓞 F)) :=
  frameBadSetG T₀ hT (Lat.image (adaptedZero Q₀ T₀ hT Ξ).g⁻¹ (stdLat F (N + 0)))

theorem good_loc_zero (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ badZero Q₀ T₀ hT Ξ) :
    locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) (adaptedZero Q₀ T₀ hT Ξ).g)⁻¹
      (std v) = std v := by
  have hloc : loc v (Lat.image (adaptedZero Q₀ T₀ hT Ξ).g⁻¹ (stdLat F (N + 0))).1 =
      locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) (adaptedZero Q₀ T₀ hT Ξ).g)⁻¹
        (std v) := by
    show loc v (glImage _ intVec) = _
    rw [loc_glImage, loc_intVec, map_inv]
  rw [← hloc]; exact (not_mem_frameBadSetG T₀ hT _ hv).2

theorem good_base_int_aux (v : HeightOneSpectrum (𝓞 F))
    (hΛ : locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) (adaptedZero Q₀ T₀ hT Ξ).g)⁻¹
      (std v) = std v) (i : Fin (N + 0)) (j : Fin N) :
    Valued.v ((locBase (r := N) (n' := 0) v Q₀ T₀ (adaptedZero Q₀ T₀ hT Ξ)) i j) ≤ 1 := by
  have hΛ' : locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) (adaptedZero Q₀ T₀ hT Ξ).g)
      (std v) = std v := locAct_eq_iff.mpr hΛ.symm
  have h1 : (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) (adaptedZero Q₀ T₀ hT Ξ).g).val *ᵥ
      stdCol v (n' := 0) j ∈ locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F))
        (adaptedZero Q₀ T₀ hT Ξ).g) (std v) := ⟨stdCol v j, stdCol_mem_std v j, rfl⟩
  rw [hΛ'] at h1
  have h2 := congrFun (mulVec_stdCol v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F))
    (adaptedZero Q₀ T₀ hT Ξ).g).val j) i
  have h3 := h1 i
  rw [neg_zero, WithZero.exp_zero] at h3
  rw [h2] at h3
  exact h3

include hQ in
/-- At a place outside `badZero` there is exactly one local orbit: $n_v = 1$. -/
theorem locCountZero_eq_one (hN : 0 < N) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ badZero Q₀ T₀ hT Ξ) :
    locCountZero Q₀ T₀ hT Ξ v = 1 := by
  classical
  have := subsingleton_GL_zero (v.adicCompletion F)
  have hQ' : (formZero (𝓞 F)).Nondegenerate := formZero_nondegenerate
  have hloc : loc v (Lat.image (adaptedZero Q₀ T₀ hT Ξ).g⁻¹ (stdLat F (N + 0))).1 =
      locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) (adaptedZero Q₀ T₀ hT Ξ).g)⁻¹
        (std v) := by
    show loc v (glImage _ intVec) = _
    rw [loc_glImage, loc_intVec, map_inv]
  have hΛ : locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) (adaptedZero Q₀ T₀ hT Ξ).g)⁻¹
      (std v) = std v := by
    rw [← hloc]; exact (not_mem_frameBadSetG T₀ hT _ hv).2
  have key : ∀ M M' : LocFrameSetG v (T₀.map (algebraMap (𝓞 F) F))
      (((adaptedZero Q₀ T₀ hT Ξ).Q').map (algebraMap (𝓞 F) F))
      (loc v (Lat.image (adaptedZero Q₀ T₀ hT Ξ).g⁻¹ (stdLat F (N + 0))).1),
      M' ∈ orbit (orthGroup (((adaptedZero Q₀ T₀ hT Ξ).Q').map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) M :=
    fun M M' => exists_smul_of_not_memG T₀ hT (adaptedZero Q₀ T₀ hT Ξ).Q' hQ'
      (Lat.image (adaptedZero Q₀ T₀ hT Ξ).g⁻¹ (stdLat F (N + 0))) hv M M'
  rw [hloc] at key
  have hbij := ThQ_bijective (r := N) (n' := 0) v Q₀ T₀ (adaptedZero Q₀ T₀ hT Ξ) hQ hT (by omega : 0 < N + 0)
  have hs : Subsingleton (LocOrbit (r := N) (n' := 0) v Q₀ T₀ (adaptedZero Q₀ T₀ hT Ξ)) := by
    refine ⟨fun o o' => hbij.1 ?_⟩
    induction o using Quotient.inductionOn with | _ y => ?_
    induction o' using Quotient.inductionOn with | _ y' => ?_
    rw [ThQ_mk, ThQ_mk]
    obtain ⟨h, hh⟩ := key (Th (r := N) (n' := 0) v Q₀ T₀ (adaptedZero Q₀ T₀ hT Ξ) y)
      (Th (r := N) (n' := 0) v Q₀ T₀ (adaptedZero Q₀ T₀ hT Ξ) y')
    obtain rfl : h = 1 := Subsingleton.elim h 1
    have hh' : Th (r := N) (n' := 0) v Q₀ T₀ (adaptedZero Q₀ T₀ hT Ξ) y =
        Th (r := N) (n' := 0) v Q₀ T₀ (adaptedZero Q₀ T₀ hT Ξ) y' := by simpa using hh
    rw [hh']
  have hn : Nonempty (LocOrbit (r := N) (n' := 0) v Q₀ T₀ (adaptedZero Q₀ T₀ hT Ξ)) :=
    ⟨Quotient.mk _ ⟨locBase (r := N) (n' := 0) v Q₀ T₀ (adaptedZero Q₀ T₀ hT Ξ),
      ⟨1, by rw [soMat_one, Matrix.one_mul]⟩, good_base_int_aux Q₀ T₀ hT Ξ v hΛ⟩⟩
  unfold locCountZero
  exact Nat.card_unique

/-! #### The dictionary between adelic orbits and families of local orbits -/

section Chain

variable (v : HeightOneSpectrum (𝓞 F))

local notation "frZ" => adaptedZero Q₀ T₀ hT Ξ

/-- **The local frame** $b_v\,\Xi$ of $b\in SO(V)(\mathbb A_f)$ at $v$ (corank zero). -/
def locFrZero (b : SOAf Q₀) : Matrix (Fin (N + 0)) (Fin N) (v.adicCompletion F) :=
  soMat v (evalSO Q₀ v b) * locBase (r := N) (n' := 0) v Q₀ T₀ frZ

theorem smul_ratFT_apply_zero (b : SOAf Q₀) (i : Fin (N + 0)) (j : Fin N) :
    ((b • ratFT Q₀ T₀ Ξ) j i) v = locFrZero Q₀ T₀ hT Ξ v b i j := by
  rw [locFrZero, locBase_adaptedZero Q₀ T₀ hT Ξ v]
  show (matV Q₀ ((1 : GInfSO Q₀), b) v *ᵥ fun k => σV v (Ξ.1 k j)) i = _
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.map_apply]
  rfl

theorem locFrZero_mul (k b : SOAf Q₀) :
    locFrZero Q₀ T₀ hT Ξ v (k * b) = soMat v (evalSO Q₀ v k) * locFrZero Q₀ T₀ hT Ξ v b := by
  rw [locFrZero, locFrZero, map_mul, soMat_mul, Matrix.mul_assoc]

end Chain

theorem mem_latHatT_smul_iff_zero (b : SOAf Q₀) :
    b • ratFT Q₀ T₀ Ξ ∈ latHatT F (N + 0) N ↔
      ∀ (v : HeightOneSpectrum (𝓞 F)) i j, Valued.v (locFrZero Q₀ T₀ hT Ξ v b i j) ≤ 1 := by
  constructor
  · intro h v i j
    have := h j i v
    rw [smul_ratFT_apply_zero Q₀ T₀ hT Ξ v b i j] at this
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp this
  · intro h j i v
    show ((b • ratFT Q₀ T₀ Ξ) j i) v ∈ _
    rw [smul_ratFT_apply_zero Q₀ T₀ hT Ξ v b i j]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (h v i j)

/-- The local integral frame of an integral $b\,\Xi$ (corank zero). -/
def locFrAtZero (b : SOAf Q₀) (hb : b • ratFT Q₀ T₀ Ξ ∈ latHatT F (N + 0) N) (v : HeightOneSpectrum (𝓞 F)) :
    locFrameSet (r := N) (n' := 0) v Q₀ T₀ (adaptedZero Q₀ T₀ hT Ξ) :=
  ⟨locFrZero Q₀ T₀ hT Ξ v b, ⟨evalSO Q₀ v b, rfl⟩, fun i j => (mem_latHatT_smul_iff_zero Q₀ T₀ hT Ξ b).mp hb v i j⟩

/-- **Orbits of integral adelic frames are determined place by place** (corank zero). -/
theorem finOrbit_rel_iff_zero (b b' : {b : SOAf Q₀ // b • ratFT Q₀ T₀ Ξ ∈ latHatT F (N + 0) N}) :
    (finOrbitSetoid (n' := 0) Q₀ T₀ Ξ).r b b' ↔ ∀ v : HeightOneSpectrum (𝓞 F),
      (locOrbitSetoid (r := N) (n' := 0) v Q₀ T₀ (adaptedZero Q₀ T₀ hT Ξ)).r (locFrAtZero Q₀ T₀ hT Ξ b.1 b.2 v)
        (locFrAtZero Q₀ T₀ hT Ξ b'.1 b'.2 v) := by
  constructor
  · intro h v
    obtain ⟨k, hk, y, hy, hky⟩ := Set.mem_smul.1 h
    rw [Set.mem_singleton_iff] at hy
    subst hy
    refine ⟨evalSO Q₀ v k, (mem_KSO_iff Q₀ k).mp hk v, ?_⟩
    show locFrZero Q₀ T₀ hT Ξ v b'.1 = soMat v (evalSO Q₀ v k) * locFrZero Q₀ T₀ hT Ξ v b.1
    rw [← locFrZero_mul]
    refine Matrix.ext fun i j => ?_
    rw [← smul_ratFT_apply_zero Q₀ T₀ hT Ξ v, ← smul_ratFT_apply_zero Q₀ T₀ hT Ξ v, mul_smul, hky]
  · intro h
    choose x hx using fun v => h v
    obtain ⟨k, hk, hkv⟩ := exists_KSO_of_fam (r := N) (n' := 0) Q₀ (fun v => ⟨x v, (hx v).1⟩)
    refine Set.mem_smul.2 ⟨k, hk, _, rfl, ?_⟩
    rw [← mul_smul]
    funext j i
    refine Subtype.ext (funext fun v => ?_)
    show (((k * b.1) • ratFT Q₀ T₀ Ξ) j i) v = ((b'.1 • ratFT Q₀ T₀ Ξ) j i) v
    rw [smul_ratFT_apply_zero Q₀ T₀ hT Ξ v, smul_ratFT_apply_zero Q₀ T₀ hT Ξ v, locFrZero_mul, hkv]
    have := (hx v).2
    simp only [locFrAtZero] at this
    rw [← this]

/-- The local orbit at $v$ of an orbit $O$ of integral adelic frames (corank zero). -/
def finToLocZero (O : FinOrbit (n' := 0) Q₀ T₀ Ξ) (v : HeightOneSpectrum (𝓞 F)) :
    LocOrbit (r := N) (n' := 0) v Q₀ T₀ (adaptedZero Q₀ T₀ hT Ξ) :=
  Quotient.mk _ (locFrAtZero Q₀ T₀ hT Ξ (Quotient.out O).1 (Quotient.out O).2 v)

theorem finToLocZero_eq (b : {b : SOAf Q₀ // b • ratFT Q₀ T₀ Ξ ∈ latHatT F (N + 0) N}) (v : HeightOneSpectrum (𝓞 F)) :
    finToLocZero Q₀ T₀ hT Ξ (Quotient.mk _ b) v = Quotient.mk _ (locFrAtZero Q₀ T₀ hT Ξ b.1 b.2 v) := by
  apply Quotient.sound
  have h : (finOrbitSetoid (n' := 0) Q₀ T₀ Ξ).r
      (Quotient.out (Quotient.mk (finOrbitSetoid (n' := 0) Q₀ T₀ Ξ) b)) b :=
    Quotient.mk_out (s := finOrbitSetoid (n' := 0) Q₀ T₀ Ξ) b
  exact (finOrbit_rel_iff_zero Q₀ T₀ hT Ξ _ _).mp h v

/-- The local orbits at the exceptional places of an orbit of integral adelic frames (corank zero). -/
def finOrbitMapZero (O : FinOrbit (n' := 0) Q₀ T₀ Ξ) :
    ∀ v : badZero Q₀ T₀ hT Ξ, LocOrbit (r := N) (n' := 0) v.1 Q₀ T₀ (adaptedZero Q₀ T₀ hT Ξ) :=
  fun v => finToLocZero Q₀ T₀ hT Ξ O v.1

include hQ in
/-- **The orbits of integral adelic frames are the families of local orbits at the exceptional places** (corank zero). -/
theorem finOrbitMapZero_bijective (hN : 0 < N) : Function.Bijective (finOrbitMapZero Q₀ T₀ hT Ξ) := by
  classical
  have hsub : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ badZero Q₀ T₀ hT Ξ →
      Subsingleton (LocOrbit (r := N) (n' := 0) v Q₀ T₀ (adaptedZero Q₀ T₀ hT Ξ)) := fun v hv =>
    (Nat.card_eq_one_iff_unique.mp (locCountZero_eq_one Q₀ hQ T₀ hT Ξ hN v hv)).1
  constructor
  · intro O O' h
    rw [← Quotient.out_eq O, ← Quotient.out_eq O']
    apply Quotient.sound
    refine (finOrbit_rel_iff_zero Q₀ T₀ hT Ξ _ _).mpr fun v => ?_
    by_cases hv : v ∈ badZero Q₀ T₀ hT Ξ
    · exact Quotient.exact (congrFun h ⟨v, hv⟩)
    · have := hsub v hv
      exact Quotient.exact (Subsingleton.elim (Quotient.mk _ _) (Quotient.mk _ _))
  · intro x
    set φ : ∀ v, SOv v Q₀ := fun v =>
      if hv : v ∈ badZero Q₀ T₀ hT Ξ then locOrbitRep (r := N) (n' := 0) v Q₀ T₀ (adaptedZero Q₀ T₀ hT Ξ) (x ⟨v, hv⟩) else 1 with hφ
    obtain ⟨c, hcS, hcn⟩ := exists_SOAf_of_fam (r := N) (n' := 0) Q₀ (badZero Q₀ T₀ hT Ξ) φ
    have hS : ∀ (v) (hv : v ∈ badZero Q₀ T₀ hT Ξ), locFrZero Q₀ T₀ hT Ξ v c =
        (Quotient.out (x ⟨v, hv⟩) : locFrameSet (r := N) (n' := 0) v Q₀ T₀ (adaptedZero Q₀ T₀ hT Ξ)).1 := by
      intro v hv
      show soMat v (evalSO Q₀ v c) * locBase (r := N) (n' := 0) v Q₀ T₀ (adaptedZero Q₀ T₀ hT Ξ) = _
      rw [hcS v hv, frPhi_spec (r := N) (n' := 0) v Q₀ T₀ (adaptedZero Q₀ T₀ hT Ξ) (Quotient.out (x ⟨v, hv⟩))]
      simp only [hφ, hv, ↓reduceDIte, locOrbitRep_eq]
    have hN' : ∀ v ∉ badZero Q₀ T₀ hT Ξ, locFrZero Q₀ T₀ hT Ξ v c =
        locBase (r := N) (n' := 0) v Q₀ T₀ (adaptedZero Q₀ T₀ hT Ξ) := fun v hv => by
      simp only [locFrZero, hcn v hv, soMat_one, Matrix.one_mul]
    have hint : c • ratFT Q₀ T₀ Ξ ∈ latHatT F (N + 0) N := by
      rw [mem_latHatT_smul_iff_zero Q₀ T₀ hT Ξ]
      intro v i j
      by_cases hv : v ∈ badZero Q₀ T₀ hT Ξ
      · rw [hS v hv]; exact (Quotient.out (x ⟨v, hv⟩)).2.2 i j
      · rw [hN' v hv]; exact good_base_int_aux Q₀ T₀ hT Ξ v (good_loc_zero Q₀ T₀ hT Ξ v hv) i j
    refine ⟨Quotient.mk _ ⟨c, hint⟩, funext fun v => ?_⟩
    show finToLocZero Q₀ T₀ hT Ξ (Quotient.mk _ ⟨c, hint⟩) v.1 = x v
    rw [finToLocZero_eq]
    conv_rhs => rw [← Quotient.out_eq (x v)]
    exact congrArg _ (Subtype.ext (hS v.1 v.2))

include hQ in
/-- **The number of orbits of integral adelic frames is the product of the local counts** (corank zero). -/
theorem tsum_one_finOrbit_zero (hN : 0 < N) :
    ∑' _O : FinOrbit (n' := 0) Q₀ T₀ Ξ, (1 : ℝ≥0∞) = ENNReal.ofReal (∏' v, (locCountZero Q₀ T₀ hT Ξ v : ℝ)) := by
  classical
  have : ∀ v : badZero Q₀ T₀ hT Ξ, Finite (LocOrbit (r := N) (n' := 0) v.1 Q₀ T₀ (adaptedZero Q₀ T₀ hT Ξ)) :=
    fun v => finite_locOrbit_zero Q₀ hQ T₀ hT Ξ hN v.1
  have e := Equiv.ofBijective _ (finOrbitMapZero_bijective Q₀ hQ T₀ hT Ξ hN)
  have : Finite (FinOrbit (n' := 0) Q₀ T₀ Ξ) := Finite.of_equiv _ e.symm
  have := Fintype.ofFinite (FinOrbit (n' := 0) Q₀ T₀ Ξ)
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, ← Nat.card_eq_fintype_card,
    Nat.card_congr e, Nat.card_pi,
    tprod_eq_prod (s := badZero Q₀ T₀ hT Ξ) (fun v hv => by
      rw [locCountZero_eq_one Q₀ hQ T₀ hT Ξ hN v hv]; simp),
    ← Nat.cast_prod, ENNReal.ofReal_natCast, ← Finset.prod_coe_sort (badZero Q₀ T₀ hT Ξ)]
  rfl

end Global

end QuadFormsKB.Tamagawa.Indefinite
