/-
# The type sum for frames as a product of local type sums

**Layer:** $F$ a number field, lattices in $F^{r+n'}$ with $T_0 \perp Q_0'$ over $\mathcal O_F$; the local types of `FrameLocal.lean`.

**Proves**
* `exists_diag_global`: a nondegenerate $T_0$ over $\mathcal O_F$ has $T_0\circ P = \langle d_0, \dots, d_{r-1}\rangle$ with $P$ integral,
  $\det P \ne 0$, all $d_i \ne 0$ (an orthogonal basis over $F$, `exists_orthogonal_basis`, with denominators cleared);
* `locFrameTypeSum_eq_one`: at the primes $\mathfrak p \nmid 2\det P\prod_i d_i$ there is one local type, of weight $1$
  (`exists_frame_isometry_of_unimodular` and the stabilizer of $E$); no condition on $Q_0'$;
* **`typeSumT_eq_prod`**: $\sum_t w(t) = \prod_{\mathfrak p \in S} W_\mathfrak p$, $S$ = `frameBadSet` (as the
  `typeSum_eq_prod`: global types are
  the families of local types at $S$, glued with `LocFamily.glue`; the weight of a glued lattice is the product of local weights,
  `relIndex_restrictedPi`).

Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.FrameRepMass
import QuadFormsKB.Tamagawa.FrameLocal
import QuadFormsKB.Tamagawa.FrameDiag

open NumberField IsDedekindDomain Matrix MulAction
open scoped RestrictedProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Frames

open QuadFormsKB.Tamagawa Lattices LocalDensity LocalDensity.DVR

variable {F : Type} [Field F] [NumberField F] {r n' : ℕ}

/-- The chosen diagonalization data of `exists_diag_global`, and **the bad primes of the frame setting**: those dividing
$2\det P\prod_i d_i$ (finitely many). -/
def frameBadSet (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) : Finset (HeightOneSpectrum (𝓞 F)) :=
  (Filter.eventually_cofinite.mp (eventually_not_mem
    (d := 2 * (Classical.choose (exists_diag_global T₀ hT)).det *
      ∏ i, Classical.choose (Classical.choose_spec (exists_diag_global T₀ hT)) i)
    (mul_ne_zero (mul_ne_zero (two_ne_zero (α := 𝓞 F))
      (Classical.choose_spec (Classical.choose_spec (exists_diag_global T₀ hT))).1)
      (Finset.prod_ne_zero_iff.mpr fun i _ =>
        (Classical.choose_spec (Classical.choose_spec (exists_diag_global T₀ hT))).2.1 i)))).toFinset

/-- The chosen integral matrix $P$ of the global diagonalization. -/
def frameP (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) : Matrix (Fin r) (Fin r) (𝓞 F) :=
  Classical.choose (exists_diag_global T₀ hT)

/-- The chosen diagonal entries $d_i$ of the global diagonalization. -/
def frameDg (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) : Fin r → 𝓞 F :=
  Classical.choose (Classical.choose_spec (exists_diag_global T₀ hT))

theorem frameP_det_ne (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) : (frameP T₀ hT).det ≠ 0 :=
  (Classical.choose_spec (Classical.choose_spec (exists_diag_global T₀ hT))).1

theorem frameDg_ne (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) (i : Fin r) : frameDg T₀ hT i ≠ 0 :=
  (Classical.choose_spec (Classical.choose_spec (exists_diag_global T₀ hT))).2.1 i

theorem frame_compMat (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) :
    T₀.compMat (frameP T₀ hT) = QuadForm.diag (frameDg T₀ hT) :=
  (Classical.choose_spec (Classical.choose_spec (exists_diag_global T₀ hT))).2.2

theorem mem_frameBadSet (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) {v : HeightOneSpectrum (𝓞 F)} :
    v ∈ frameBadSet T₀ hT ↔ 2 * (frameP T₀ hT).det * ∏ i, frameDg T₀ hT i ∈ v.asIdeal := by
  simp [frameBadSet, frameP, frameDg]

theorem evalIn_blockForm_stdFrameMat {K : Type*} [CommRing K] (T : QuadForm F r) (Q' : QuadForm F n') [Algebra F K]
    (z : Fin r → K) :
    (blockForm T Q').evalIn K ((stdFrameMat : Matrix (Fin (r + n')) (Fin r) K) *ᵥ z) = T.evalIn K z := by
  rw [evalIn_blockForm]
  have h1 : (fun i => ((stdFrameMat : Matrix (Fin (r + n')) (Fin r) K) *ᵥ z) (Fin.castAdd n' i)) = z := by
    funext i
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  have h2 : (fun j => ((stdFrameMat : Matrix (Fin (r + n')) (Fin r) K) *ᵥ z) (Fin.natAdd r j)) = 0 := by
    funext j
    simp [Matrix.mulVec, dotProduct]
  rw [h1, h2]
  have : Q'.evalIn K 0 = 0 := by simp [QuadForm.evalIn]
  rw [this, add_zero]

/-- **Transitivity at the good primes:** for $\mathfrak p \notin S$, $O(Q')(F_\mathfrak p)$ is transitive on $Y_\mathfrak p$
(`exists_frame_isometry_of_unimodular`, the stabilizer of $E$ and `exists_intRep_eq`). -/
theorem exists_smul_locFrameStdPt (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) (Q₀' : QuadForm (𝓞 F) n')
    (hQ' : Q₀'.Nondegenerate)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ frameBadSet T₀ hT) :
    ∀ M : LocFrameSet v (T₀.map (algebraMap (𝓞 F) F)) (Q₀'.map (algebraMap (𝓞 F) F)),
    ∃ h : orthGroup (Q₀'.map (algebraMap (𝓞 F) F)) (v.adicCompletion F),
      h • locFrameStdPt v (T₀.map (algebraMap (𝓞 F) F)) (Q₀'.map (algebraMap (𝓞 F) F)) = M := by
  classical
  set T := T₀.map (algebraMap (𝓞 F) F) with hTdef
  set Q' := Q₀'.map (algebraMap (𝓞 F) F) with hQdef
  intro M
  -- the unit conditions at v
  have hvI := (mem_frameBadSet T₀ hT).not.mp hv
  have hI := v.isPrime
  have h2I : (2 : 𝓞 F) ∉ v.asIdeal := fun h => hvI (v.asIdeal.mul_mem_right _ (v.asIdeal.mul_mem_right _ h))
  have hdetI : (frameP T₀ hT).det ∉ v.asIdeal := fun h =>
    hvI (v.asIdeal.mul_mem_right _ (v.asIdeal.mul_mem_left _ h))
  have hdgI : ∀ i, frameDg T₀ hT i ∉ v.asIdeal := fun i h => hvI (by
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (frameDg T₀ hT) (Finset.mem_univ i)
    rw [hc]
    exact v.asIdeal.mul_mem_left _ (v.asIdeal.mul_mem_right _ h))
  -- notation
  set Fv := v.adicCompletion F
  set 𝔬 := v.adicCompletionIntegers F
  obtain ⟨⟨g, hgO⟩, hg⟩ := M.2.1
  have hcolM : ∀ j, ∃ y : Fin (r + n') → v.adicCompletion F, y ∈ std v ∧
      g.val *ᵥ y = stdCol v (n' := n') j := by
    intro j
    have he := M.2.2 j
    rw [← hg] at he
    obtain ⟨y, hy, hgy⟩ := he
    exact ⟨y, hy, hgy⟩
  choose y hy hgy using hcolM
  have hyv : ∀ j i, Valued.v (y j i) ≤ 1 := by
    intro j i; have := hy j i; rwa [neg_zero, WithZero.exp_zero] at this
  let Xo : Matrix (Fin (r + n')) (Fin r) (v.adicCompletionIntegers F) :=
    Matrix.of fun l j => ⟨y j l, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hyv j l)⟩
  have hgX : g.val * Xo.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) =
      stdFrameMat := by
    refine Matrix.ext fun l j => ?_
    exact congrFun (hgy j) l
  -- the integral model
  set Tp := NF.Qp v T₀ with hTp
  set Qp' := NF.Qp v Q₀' with hQp
  set Qo := blockForm Tp Qp' with hQo
  have hmodel : IsIntModel v (blockForm T Q') Qo := by
    intro z
    have e1 : blockForm T Q' = (blockForm T₀ Q₀').map (algebraMap (𝓞 F) F) := (map_blockForm _ _ _).symm
    rw [e1, evalIn_coe_o v (blockForm T₀ Q₀') z]
    simp only [NF.Qp, hQo, map_blockForm]
    rfl
  have hQond : Qo.Nondegenerate := by
    rw [hQo, QuadForm.Nondegenerate, det_hessian_blockForm]
    exact mul_ne_zero (NF.nondegenerate_Qp v hT) (NF.nondegenerate_Qp v hQ')
  have hXQ : Qo.compMat Xo = Tp := by
    apply QuadForm.eq_of_eval_eq
    intro z
    apply Subtype.ext
    show ((Qo.compMat Xo).eval z : v.adicCompletion F) = (Tp.eval z : v.adicCompletion F)
    have hcv : (fun i => ((Xo *ᵥ z) i : v.adicCompletion F)) =
        Xo.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) *ᵥ fun i => (z i : v.adicCompletion F) := by
      funext i; exact RingHom.map_mulVec (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) Xo z i
    rw [QuadForm.eval_compMat, ← hmodel (Xo *ᵥ z), hcv, hTp, ← evalIn_coe_o v T₀ z,
      ← evalIn_mulVec_of_mem (blockForm T Q') hgO, mulVec_mulVec, hgX, evalIn_blockForm_stdFrameMat]
  have hx : formF Qo (fun p : Fin (r + n') × Fin r => Xo p.1 p.2) = tc Tp := by
    rw [formF_eq_tc_iff]; exact hXQ
  have hx' : formF Qo (stdFrame (A := v.adicCompletionIntegers F)) = tc Tp := formF_stdFrame Tp Qp'
  -- the integral isometry
  have hPdet : ((frameP T₀ hT).map (NF.ι v)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact NF.ι_ne_zero v (frameP_det_ne T₀ hT)
  have hPd : Tp.compMat ((frameP T₀ hT).map (NF.ι v)) = QuadForm.diag (fun i => NF.ι v (frameDg T₀ hT i)) := by
    rw [hTp, NF.Qp, QuadForm.map_compMat, frame_compMat]
    ext i j
    simp [QuadForm.map, QuadForm.diag, Matrix.diagonal_apply]
  have hdgU : ∀ i, IsUnit (NF.ι v (frameDg T₀ hT i)) := fun i => isUnit_ι_of_not_mem v (hdgI i)
  have h2 : ¬ NF.π v ∣ (2 : v.adicCompletionIntegers F) := by
    intro h
    rw [← map_ofNat (NF.ι v) 2] at h
    exact h2I ((NF.π_dvd_ι_iff v 2).mp h)
  obtain ⟨M0, hM0, hM0x⟩ := exists_frame_isometry_of_unimodular (NF.irreducible_π v) h2 Qo Tp hPdet hPd hdgU hx hx'
  have hM0X : M0 * Xo = stdFrameMat := by
    have := toMat_frameMat_mulVec (r := r) M0 (fun p : Fin (r + n') × Fin r => Xo p.1 p.2)
    rw [hM0x, toMat_stdFrame] at this
    exact this.symm
  obtain ⟨κ, hκ⟩ := exists_intRep_eq v hmodel hQond M0 hM0
  have hstd𝔬 : (stdFrameMat : Matrix (Fin (r + n')) (Fin r) (v.adicCompletionIntegers F)).map
      (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) = stdFrameMat := by
    refine Matrix.ext fun l j => ?_
    simp only [Matrix.map_apply, stdFrameMat, Matrix.of_apply]
    split_ifs <;> simp
  have hkX : ((κ : orthGroup (blockForm T Q') (v.adicCompletion F)) : GL (Fin (r + n')) (v.adicCompletion F)).val *
      Xo.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) = stdFrameMat := by
    rw [← intRep_map v (blockForm T Q') κ, hκ, ← Matrix.map_mul, hM0X, hstd𝔬]
  have hTF : T.hessian.det ≠ 0 := by
    rw [hTdef, hessian_map_alg, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hT
  have hTdet : (T.hessian.map (algebraMap F (v.adicCompletion F))).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).mpr hTF
  set k : orthGroup (blockForm T Q') (v.adicCompletion F) := (κ : orthGroup (blockForm T Q') (v.adicCompletion F))
    with hk
  set g' : orthGroup (blockForm T Q') (v.adicCompletion F) := ⟨g, hgO⟩ with hg'
  have hγ : ((k * g'⁻¹ : orthGroup (blockForm T Q') (v.adicCompletion F)) :
      GL (Fin (r + n')) (v.adicCompletion F)).val * stdFrameMat = stdFrameMat := by
    have h1 : (g⁻¹ : GL (Fin (r + n')) (v.adicCompletion F)).val * stdFrameMat =
        Xo.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) := by
      calc (g⁻¹ : GL (Fin (r + n')) (v.adicCompletion F)).val * stdFrameMat
          = (g⁻¹ : GL (Fin (r + n')) (v.adicCompletion F)).val * (g.val *
              Xo.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))) := by rw [hgX]; rfl
        _ = ((g⁻¹ : GL (Fin (r + n')) (v.adicCompletion F)).val * g.val) *
              Xo.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) :=
            (Matrix.mul_assoc _ _ _).symm
        _ = _ := by rw [Units.inv_mul, Matrix.one_mul]
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, show ((g' : GL _ _)) = g from rfl]
    calc _ = ((k : GL (Fin (r + n')) (v.adicCompletion F)).val *
            (g⁻¹ : GL (Fin (r + n')) (v.adicCompletion F)).val) * stdFrameMat := rfl
      _ = (k : GL (Fin (r + n')) (v.adicCompletion F)).val *
            ((g⁻¹ : GL (Fin (r + n')) (v.adicCompletion F)).val * stdFrameMat) := Matrix.mul_assoc _ _ _
      _ = stdFrameMat := (congrArg (fun A => (k : GL (Fin (r + n')) (v.adicCompletion F)).val * A) h1).trans hkX
  obtain ⟨h, hh⟩ := exists_orthEmbB_eq T Q' (v.adicCompletion F) hTdet _ hγ
  refine ⟨h⁻¹, Subtype.ext ?_⟩
  show locAct v (orthEmbB T Q' (v.adicCompletion F) h⁻¹ : GL (Fin (r + n')) (v.adicCompletion F)) (std v) = M.1
  have hkinv : locAct v ((k⁻¹ : orthGroup (blockForm T Q') (v.adicCompletion F)) :
      GL (Fin (r + n')) (v.adicCompletion F)) (std v) = std v := (κ⁻¹).2
  rw [map_inv, hh, ← hg, _root_.mul_inv_rev, inv_inv, Subgroup.coe_mul, locAct_mul, hkinv]

/-- **One local type at the good primes:** for $\mathfrak p \notin S$ every $M \in Y_\mathfrak p$ is $\mathrm{diag}(1_r, h)\,\mathfrak o_\mathfrak p^{r+n'}$,
so $W_\mathfrak p = 1$ (cf. O'Meara 1963, §92, pp. 246–250). Here $Q_0'$ is nondegenerate (added hypothesis, needed so that
integral isometries of $T_0\perp Q_0'$ are invertible). -/
@[kb "omeara1963" "§92, pp. 246–249 (non-dyadic lattices)"]
theorem locFrameTypeSum_eq_one (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) (Q₀' : QuadForm (𝓞 F) n')
    (hQ' : Q₀'.Nondegenerate)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ frameBadSet T₀ hT) :
    locFrameTypeSum v (T₀.map (algebraMap (𝓞 F) F)) (Q₀'.map (algebraMap (𝓞 F) F)) = 1 :=
  locFrameTypeSum_eq_one_of_transitive v _ _ (exists_smul_locFrameStdPt T₀ hT Q₀' hQ' hv)

/-! ### The weights of the global types do not depend on the representative -/

section Weights

open Lattices

variable {F : Type} [Field F] [NumberField F] {r n' : ℕ} (T : QuadForm F r) (Q' : QuadForm F n') (L : Lat F (r + n'))

/-- **The weight of a lattice** $M \in Y$ (frames): $w(M) = [K_M : K_M\cap K_0']^{-1}[K_0' : K_M\cap K_0']$; `typeWeightT t` is
`compWeightT t.out`. -/
def compWeightT (y : CompSetT T Q' L) : ℝ :=
  ((stabilizer (OAf Q') y).relIndex (locStab Q' (stdLat F n')) : ℝ) /
    ((locStab Q' (stdLat F n')).relIndex (stabilizer (OAf Q') y) : ℝ)

theorem typeWeightT_eq_compWeightT (t : orbitRel.Quotient (OAf Q') (CompSetT T Q' L)) :
    typeWeightT T Q' L t = compWeightT T Q' L t.out := rfl

theorem dcMass_compSetT_eq (hpd' : IsTotallyPosDef Q') (hLi' : IsIntegral Q' (stdLat F n').1)
    (y : CompSetT T Q' L) :
    dcMass (ratPoints Q') (stabilizer (OAf Q') y) = mass Q' (stdLat F n') * compWeightT T Q' L y := by
  have hK := commensurable_stabilizer_compSetT T Q' L y
  have := finite_orbits hpd' (stdLat F n') hLi'
  have h := dcMass_mul_idxVol (ratPoints Q') (locStab Q' (stdLat F n')) (stabilizer (OAf Q') y) 1 hK
    (finite_stabilizer hpd' (stdLat F n') hLi')
  rw [one_mul, ← mass_eq_dcMass] at h
  have h1 : ((stabilizer (OAf Q') y).relIndex (locStab Q' (stdLat F n')) : ℝ) ≠ 0 := by
    exact_mod_cast hK.1.relIndex_ne_zero
  have h2 : ((locStab Q' (stdLat F n')).relIndex (stabilizer (OAf Q') y) : ℝ) ≠ 0 := by
    exact_mod_cast hK.2.relIndex_ne_zero
  unfold idxVol at h
  unfold compWeightT
  rw [← h]
  field_simp

theorem compWeightT_smul (hpd' : IsTotallyPosDef Q') (hLi' : IsIntegral Q' (stdLat F n').1) (h : OAf Q')
    (y : CompSetT T Q' L) : compWeightT T Q' L (h • y) = compWeightT T Q' L y := by
  have h1 := dcMass_compSetT_eq T Q' L hpd' hLi' (h • y)
  rw [stabilizer_smul_eq_stabilizer_map_conj, dcMass_map_conj, dcMass_compSetT_eq T Q' L hpd' hLi' y] at h1
  exact (mul_left_cancel₀ (mass_pos hpd' (stdLat F n') hLi').ne' h1).symm

theorem compWeightT_of_mem_orbit (hpd' : IsTotallyPosDef Q') (hLi' : IsIntegral Q' (stdLat F n').1)
    {y y' : CompSetT T Q' L} (h : y' ∈ orbit (OAf Q') y) : compWeightT T Q' L y' = compWeightT T Q' L y := by
  obtain ⟨h, rfl⟩ := h
  exact compWeightT_smul T Q' L hpd' hLi' h y

end Weights

/-! ### Local components of the global type set -/

section Components

open Lattices

variable {F : Type} [Field F] [NumberField F] {r n' : ℕ} (T : QuadForm F r) (Q' : QuadForm F n')

theorem locVec_stdFrameCol (v : HeightOneSpectrum (𝓞 F)) (j : Fin r) :
    locVec v (fun i => (stdFrameMat : Matrix (Fin (r + n')) (Fin r) F) i j) = stdCol v (n' := n') j := by
  funext i
  by_cases h : i = Fin.castAdd n' j <;> simp [stdCol, stdFrameMat, locVec, h]

/-- **The local component** $M_\mathfrak p \in Y_\mathfrak p$ of $M \in Y$ ($L = \mathcal O_F^{r+n'}$). -/
def locOfT (v : HeightOneSpectrum (𝓞 F)) (M : CompSetT T Q' (stdLat F (r + n'))) : LocFrameSet v T Q' :=
  ⟨loc v M.1.1, by
      obtain ⟨g, hg, hgM⟩ := M.2.1 v
      rw [loc_stdLat] at hgM
      exact ⟨⟨g, hg⟩, hgM⟩,
    fun j => by
      rw [← locVec_stdFrameCol v j]; exact locVec_mem_loc v (M.2.2 j)⟩

theorem locOfT_val (v : HeightOneSpectrum (𝓞 F)) (M : CompSetT T Q' (stdLat F (r + n'))) :
    (locOfT T Q' v M).1 = loc v M.1.1 := rfl

theorem locOfT_smul (v : HeightOneSpectrum (𝓞 F)) (h : OAf Q') (M : CompSetT T Q' (stdLat F (r + n'))) :
    locOfT T Q' v (h • M) = h v • locOfT T Q' v M := by
  refine Subtype.ext ?_
  rw [LocFrameSet.smul_val, locOfT_val, locOfT_val, CompSetT.smul_val]
  exact loc_latSMul (blockForm T Q') (orthEmbBAf T Q' h) M.1 v

/-- **Global orbits are determined prime by prime** (frames). -/
theorem mem_orbit_compSetT_iff (M M' : CompSetT T Q' (stdLat F (r + n'))) :
    M' ∈ orbit (OAf Q') M ↔
      ∀ v, locOfT T Q' v M' ∈ orbit (orthGroup Q' (v.adicCompletion F)) (locOfT T Q' v M) := by
  classical
  constructor
  · rintro ⟨h, rfl⟩ v
    exact ⟨h v, (locOfT_smul T Q' v h M).symm⟩
  · intro hloc
    choose hv hhv using hloc
    let hp : (v : HeightOneSpectrum (𝓞 F)) → orthGroup Q' (v.adicCompletion F) := fun v =>
      if loc v M.1.1 = loc v M'.1.1 then 1 else hv v
    have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, hp v ∈ stdStab Q' v := by
      filter_upwards [loc_eventually_std M.1.2, loc_eventually_std M'.1.2] with v h1 h2
      have : loc v M.1.1 = loc v M'.1.1 := h1.trans h2.symm
      simp only [hp, this, ↓reduceIte]
      exact (stdStab Q' v).one_mem
    let hA : OAf Q' := ⟨hp, hev⟩
    refine ⟨hA, Subtype.ext (Subtype.ext (loc_injective (hA • M).1.2 M'.1.2 fun v => ?_))⟩
    have e := locOfT_smul T Q' v hA M
    have e2 : loc v (hA • M).1.1 = (locOfT T Q' v (hA • M)).1 := rfl
    rw [e2, e]
    show (hp v • locOfT T Q' v M).1 = _
    simp only [hp]
    split_ifs with heq
    · rw [one_smul]; exact heq
    · have := congrArg Subtype.val (hhv v)
      exact this

end Components

/-! ### Factorization of the type sum -/

section Factor

open Lattices

variable {F : Type} [Field F] [NumberField F] {r n' : ℕ} (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate)
  (Q₀' : QuadForm (𝓞 F) n') (hQ' : Q₀'.Nondegenerate)

local notation "TF" => T₀.map (algebraMap (𝓞 F) F)
local notation "QF'" => Q₀'.map (algebraMap (𝓞 F) F)
local notation "Lstd" => stdLat F (r + n')
local notation "S" => frameBadSet T₀ hT

/-- **Global types to local types at the bad primes.** -/
def typeMapT : orbitRel.Quotient (OAf QF') (CompSetT TF QF' Lstd) → ((v : S) → LocFrameTypes v TF QF') :=
  Quotient.lift (fun M v => Quotient.mk'' (locOfT TF QF' v M)) (fun a b hab => funext fun v => by
    exact Quotient.sound' ((mem_orbit_compSetT_iff TF QF' b a).mp hab v))

theorem typeMapT_mk (M : CompSetT TF QF' Lstd) (v : S) :
    typeMapT T₀ hT Q₀' (Quotient.mk'' M) v = Quotient.mk'' (locOfT TF QF' v M) := rfl

theorem typeMapT_injective (hQ' : Q₀'.Nondegenerate) : Function.Injective (typeMapT T₀ hT Q₀') := by
  intro t t' h
  induction t using Quotient.inductionOn' with | h M => ?_
  induction t' using Quotient.inductionOn' with | h M' => ?_
  apply Quotient.sound'
  show M ∈ orbit (OAf QF') M'
  rw [mem_orbit_compSetT_iff]
  intro v
  by_cases hv : v ∈ S
  · have := congrFun h ⟨v, hv⟩
    rw [typeMapT_mk, typeMapT_mk] at this
    exact Quotient.exact' this
  · obtain ⟨g, hg⟩ := exists_smul_locFrameStdPt T₀ hT Q₀' hQ' hv (locOfT TF QF' v M)
    obtain ⟨g', hg'⟩ := exists_smul_locFrameStdPt T₀ hT Q₀' hQ' hv (locOfT TF QF' v M')
    exact ⟨g * g'⁻¹, by show (g * g'⁻¹) • _ = _; rw [mul_smul, ← hg', inv_smul_smul, hg]⟩

open Classical in
/-- The local family glued from representatives of local types at the bad primes. -/
def glueFamT (f : (v : S) → LocFrameTypes v TF QF') : LocFamily F (r + n') where
  M v := if hv : v ∈ S then (locFrameRep v TF QF' (f ⟨v, hv⟩)).1 else std v
  isLattice v := by
    split_ifs with hv
    · obtain ⟨g, hg⟩ := (locFrameRep v TF QF' (f ⟨v, hv⟩)).2.1
      rw [← hg]
      exact locAct_isLattice _ (isLattice_of_bounds v le_rfl le_rfl)
    · exact isLattice_of_bounds v le_rfl le_rfl
  eventually_std := by
    filter_upwards [(S).finite_toSet.compl_mem_cofinite] with v hv
    simp only [show v ∉ S from hv, ↓reduceDIte]

open Classical in
/-- **The glued lattice** with prescribed local types. -/
def glueCompT (f : (v : S) → LocFrameTypes v TF QF') : CompSetT TF QF' Lstd :=
  ⟨⟨(glueFamT T₀ hT Q₀' f).glue, (glueFamT T₀ hT Q₀' f).glue_isLattice⟩, by
      intro v
      rw [loc_stdLat, LocFamily.loc_glue]
      show ∃ g ∈ _, _ = if hv : v ∈ S then _ else _
      split_ifs with hv
      · obtain ⟨g, hg⟩ := (locFrameRep v TF QF' (f ⟨v, hv⟩)).2.1
        exact ⟨g, g.2, hg⟩
      · exact ⟨1, (orthGroup _ _).one_mem, locAct_one _⟩,
    fun j => by
      rw [mem_iff_forall_loc (glueFamT T₀ hT Q₀' f).glue_isLattice]
      intro v
      rw [LocFamily.loc_glue, locVec_stdFrameCol]
      show _ ∈ if hv : v ∈ S then _ else _
      split_ifs with hv
      · exact (locFrameRep v TF QF' (f ⟨v, hv⟩)).2.2 j
      · exact stdCol_mem_std v j⟩

theorem locOfT_glueCompT (f : (v : S) → LocFrameTypes v TF QF') (v : S) :
    locOfT TF QF' v (glueCompT T₀ hT Q₀' f) = locFrameRep v TF QF' (f v) := by
  classical
  apply Subtype.ext
  rw [locOfT_val]
  show loc (v : HeightOneSpectrum (𝓞 F)) (glueFamT T₀ hT Q₀' f).glue = _
  rw [LocFamily.loc_glue]
  show (if hv : (v : HeightOneSpectrum (𝓞 F)) ∈ S then _ else _) = _
  simp only [v.2, ↓reduceDIte]

theorem locOfT_glueCompT_of_not_mem (f : (v : S) → LocFrameTypes v TF QF') {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ S) : locOfT TF QF' v (glueCompT T₀ hT Q₀' f) = locFrameStdPt v TF QF' := by
  classical
  apply Subtype.ext
  rw [locOfT_val]
  show loc v (glueFamT T₀ hT Q₀' f).glue = _
  rw [LocFamily.loc_glue]
  show (if hv : v ∈ S then _ else _) = _
  simp only [hv, ↓reduceDIte]
  rfl

theorem typeMapT_glueCompT (f : (v : S) → LocFrameTypes v TF QF') :
    typeMapT T₀ hT Q₀' (Quotient.mk'' (glueCompT T₀ hT Q₀' f)) = f := by
  funext v
  rw [typeMapT_mk, locOfT_glueCompT, locFrameRep_mk]

/-- **Global types = families of local types at the bad primes.** -/
def typeEquivT : orbitRel.Quotient (OAf QF') (CompSetT TF QF' Lstd) ≃ ((v : S) → LocFrameTypes v TF QF') :=
  Equiv.ofBijective _ ⟨typeMapT_injective T₀ hT Q₀' hQ', fun f => ⟨_, typeMapT_glueCompT T₀ hT Q₀' f⟩⟩

/-- **The global weight of a glued lattice is the product of the local weights.** -/
theorem compWeightT_glueCompT (f : (v : S) → LocFrameTypes v TF QF') :
    compWeightT TF QF' Lstd (glueCompT T₀ hT Q₀' f) =
      ∏ v : S, locFrameWeight v TF QF' (locFrameRep v TF QF' (f v)) := by
  classical
  set y := glueCompT T₀ hT Q₀' f
  set A' : (v : HeightOneSpectrum (𝓞 F)) → Subgroup (orthGroup QF' (v.adicCompletion F)) :=
    fun v => stabilizer (orthGroup QF' (v.adicCompletion F)) (locOfT TF QF' v y)
  have hA : ∀ v ∉ S, A' v = stdStab QF' v := by
    intro v hv
    simp only [A']
    rw [locOfT_glueCompT_of_not_mem T₀ hT Q₀' f hv, stabilizer_locFrameStdPt]
  have hB : ∀ v ∉ S, stdStab QF' v = stdStab QF' v := fun _ _ => rfl
  have hAm : ∀ h, h ∈ stabilizer (OAf QF') y ↔ ∀ v, h v ∈ A' v := by
    intro h
    rw [stabilizer_compSetT, Subgroup.mem_comap]
    show (∀ v, _ = _) ↔ _
    refine forall_congr' fun v => ?_
    simp only [A', mem_stabilizer_iff]
    constructor
    · intro hh; exact Subtype.ext hh
    · intro hh; exact congrArg Subtype.val hh
  have hBm : ∀ h, h ∈ locStab QF' (stdLat F n') ↔ ∀ v, h v ∈ stdStab QF' v := mem_locStab_intVec QF'
  have e1 := relIndex_restrictedPi S A' (fun v => stdStab QF' v) hA hB _ _ hAm hBm
  have e2 := relIndex_restrictedPi S (fun v => stdStab QF' v) A' hB hA _ _ hBm hAm
  unfold compWeightT
  rw [e1, e2, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib, ← Finset.prod_coe_sort S]
  refine Finset.prod_congr rfl fun v _ => ?_
  simp only [A', locFrameWeight]
  rw [locOfT_glueCompT]

end Factor

theorem isIntegral_stdLat_map {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) :
    IsIntegral (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F N).1 := by
  intro x hx
  obtain ⟨y', rfl⟩ := mem_intVec_iff_exists.mp hx
  refine ⟨Q₀.eval y', ?_⟩
  show _ = (Q₀.map (algebraMap (𝓞 F) F)).evalIn F (intCoe y')
  rw [← eval_map_comp]

theorem nondeg_map_alg {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) :
    Q₀.Nondegenerate ↔ (Q₀.map (algebraMap (𝓞 F) F)).Nondegenerate := by
  have h : (Q₀.map (algebraMap (𝓞 F) F)).hessian = Q₀.hessian.map (algebraMap (𝓞 F) F) := by
    ext i j; simp [QuadForm.hessian, QuadForm.map]
  rw [QuadForm.Nondegenerate, QuadForm.Nondegenerate, h, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).symm

theorem isTotallyPosDef_of_blockForm_right {T : QuadForm F r} {Q' : QuadForm F n'}
    (h : IsTotallyPosDef (blockForm T Q')) : IsTotallyPosDef Q' := by
  intro x hx
  have h1 : (Fin.append (0 : Fin r → F) x : Fin (r + n') → F) ≠ 0 := by
    intro h0; apply hx; funext j
    simpa using congrFun h0 (Fin.natAdd r j)
  have := h _ h1
  rw [QuadForm.eval, evalIn_blockForm] at this
  simpa [Fin.append, QuadForm.evalIn] using this

/-- **The type sum factors over the bad primes** (Weil 1982, §3.5 [unverified locator]): for $T_0\perp Q_0'$ totally positive definite,
$$\sum_{t\in O(Q')(\mathbb A_f)\backslash Y} w(t) = \prod_{\mathfrak p \in S} W_\mathfrak p.$$ -/
@[kb "weil1982" "§3.5 (type sum as a product of local sums) [unverified locator]"]
theorem typeSumT_eq_prod (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) (Q₀' : QuadForm (𝓞 F) n')
    (hpd : IsTotallyPosDef ((blockForm T₀ Q₀').map (algebraMap (𝓞 F) F))) :
    ∑ᶠ t : orbitRel.Quotient (OAf (Q₀'.map (algebraMap (𝓞 F) F)))
        (CompSetT (T₀.map (algebraMap (𝓞 F) F)) (Q₀'.map (algebraMap (𝓞 F) F)) (stdLat F (r + n'))),
      typeWeightT (T₀.map (algebraMap (𝓞 F) F)) (Q₀'.map (algebraMap (𝓞 F) F)) (stdLat F (r + n')) t =
    ∏ v ∈ frameBadSet T₀ hT, locFrameTypeSum v (T₀.map (algebraMap (𝓞 F) F)) (Q₀'.map (algebraMap (𝓞 F) F)) := by
  classical
  have hpd₀ : IsTotallyPosDef (blockForm (T₀.map (algebraMap (𝓞 F) F)) (Q₀'.map (algebraMap (𝓞 F) F))) := by
    have := hpd
    rw [map_blockForm] at this
    exact this
  have hpd' := isTotallyPosDef_of_blockForm_right hpd₀
  have hLi : IsIntegral (blockForm (T₀.map (algebraMap (𝓞 F) F)) (Q₀'.map (algebraMap (𝓞 F) F)))
      (stdLat F (r + n')).1 := by
    rw [← map_blockForm]; exact isIntegral_stdLat_map _
  have hLi' : IsIntegral (Q₀'.map (algebraMap (𝓞 F) F)) (stdLat F n').1 := isIntegral_stdLat_map _
  have hQ' : Q₀'.Nondegenerate := (nondeg_map_alg Q₀').mpr hpd'.nondegenerate
  have hfin := finite_typesT (T₀.map (algebraMap (𝓞 F) F)) (Q₀'.map (algebraMap (𝓞 F) F)) (stdLat F (r + n'))
    hpd₀ hLi ((nondeg_map_alg T₀).mp hT)
  have hfinP : Finite ((v : frameBadSet T₀ hT) → LocFrameTypes v (T₀.map (algebraMap (𝓞 F) F))
      (Q₀'.map (algebraMap (𝓞 F) F))) := Finite.of_equiv _ (typeEquivT T₀ hT Q₀' hQ')
  have hfinv : ∀ v : frameBadSet T₀ hT, Finite (LocFrameTypes v (T₀.map (algebraMap (𝓞 F) F))
      (Q₀'.map (algebraMap (𝓞 F) F))) := by
    intro v
    let f₀ : (v : frameBadSet T₀ hT) → LocFrameTypes v (T₀.map (algebraMap (𝓞 F) F))
      (Q₀'.map (algebraMap (𝓞 F) F)) := fun w => Quotient.mk'' (locFrameStdPt (w : HeightOneSpectrum (𝓞 F)) _ _)
    exact Finite.of_injective (fun x => Function.update f₀ v x) (Function.update_injective f₀ v)
  let _ : Fintype (orbitRel.Quotient (OAf (Q₀'.map (algebraMap (𝓞 F) F)))
    (CompSetT (T₀.map (algebraMap (𝓞 F) F)) (Q₀'.map (algebraMap (𝓞 F) F)) (stdLat F (r + n')))) :=
    Fintype.ofFinite _
  let _ : ∀ v : frameBadSet T₀ hT, Fintype (LocFrameTypes v (T₀.map (algebraMap (𝓞 F) F))
    (Q₀'.map (algebraMap (𝓞 F) F))) := fun v => Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  have step : ∀ t, typeWeightT (T₀.map (algebraMap (𝓞 F) F)) (Q₀'.map (algebraMap (𝓞 F) F)) (stdLat F (r + n')) t =
      compWeightT (T₀.map (algebraMap (𝓞 F) F)) (Q₀'.map (algebraMap (𝓞 F) F)) (stdLat F (r + n'))
        (glueCompT T₀ hT Q₀' (typeEquivT T₀ hT Q₀' hQ' t)) := by
    intro t
    rw [typeWeightT_eq_compWeightT]
    refine compWeightT_of_mem_orbit _ _ _ hpd' hLi' ?_
    have h1 : (Quotient.mk'' (glueCompT T₀ hT Q₀' (typeEquivT T₀ hT Q₀' hQ' t)) :
        orbitRel.Quotient (OAf (Q₀'.map (algebraMap (𝓞 F) F)))
          (CompSetT (T₀.map (algebraMap (𝓞 F) F)) (Q₀'.map (algebraMap (𝓞 F) F)) (stdLat F (r + n')))) = t :=
      typeMapT_injective T₀ hT Q₀' hQ' (typeMapT_glueCompT T₀ hT Q₀' _)
    have h2 : (Quotient.mk'' t.out : orbitRel.Quotient (OAf (Q₀'.map (algebraMap (𝓞 F) F)))
          (CompSetT (T₀.map (algebraMap (𝓞 F) F)) (Q₀'.map (algebraMap (𝓞 F) F)) (stdLat F (r + n')))) =
        Quotient.mk'' (glueCompT T₀ hT Q₀' (typeEquivT T₀ hT Q₀' hQ' t)) := by
      rw [h1, Quotient.out_eq']
    exact Quotient.exact' h2
  rw [Finset.sum_congr rfl fun t _ => step t,
    Equiv.sum_comp (typeEquivT T₀ hT Q₀' hQ') (fun f => compWeightT (T₀.map (algebraMap (𝓞 F) F))
      (Q₀'.map (algebraMap (𝓞 F) F)) (stdLat F (r + n')) (glueCompT T₀ hT Q₀' f))]
  simp_rw [compWeightT_glueCompT]
  rw [← Finset.prod_coe_sort (frameBadSet T₀ hT)]
  simp_rw [locFrameTypeSum, finsum_eq_sum_of_fintype]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

end QuadFormsKB.Tamagawa.Frames
