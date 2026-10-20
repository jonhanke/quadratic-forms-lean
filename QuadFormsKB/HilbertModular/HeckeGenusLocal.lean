/-
# Kneser neighbours stay in the genus over $\mathcal O_F$ (PID)

**Main theorem** (`nbrInGenus_of_pid`): for $F$ a number field with $\mathcal O_F$ a PID, $Q_0$ a form over $\mathcal O_F$ and $\pi$ a prime with
$\pi \nmid 2\det H(Q_0)$, every $\pi$-neighbour $M'$ (`Nbr.IsNbrL`) of a lattice $M$ in the genus of $\mathcal O_F^n$ is in that genus
(`NbrInGenus Q₀ π`; Kneser 1957, Satz 1 [unverified]; over $\mathbb Q$: `Siegel.Kneser.sameGenus_of_neighbor`). This discharges the
hypothesis of `HeckeGenus.lean`.

*Proof.* Write $M = \gamma\mathcal O_F^n$ and $M' = \gamma N$, $N = L(\vec v)$ the explicit $\pi$-neighbour of $\mathcal O_F^n$ for the Gram form $Q_\gamma$;
$N = \delta\mathcal O_F^n$ (PID).
* At $\mathfrak q \ne (\pi)$, $\pi$ is a unit and $\pi\mathcal O_F^n \subseteq N \subseteq \pi^{-1}\mathcal O_F^n$, so $N_\mathfrak q = \mathfrak o_\mathfrak q^n$
  (`loc_nbLat_of_ne`) and $M'_\mathfrak q = M_\mathfrak q$.
* At $\mathfrak p = (\pi)$: the Gram form $Q_{\gamma\delta}$ of $M'$ is unimodular at $\pi$ (`not_dvd_det_gram_nbLat`: by the self-duality of
  $L(\vec v)$, `Nbr.eq_smul_of_bv_dvd`, a vector in the kernel of $\bar G$ would lie in $\pi N$), and $Q_{\gamma\delta}(x) = Q_\gamma(\delta x)$ on
  $F_\mathfrak p^n$; two unimodular forms isometric over $F_\mathfrak p$ are isometric over $\mathfrak o_\mathfrak p$
  (`Nbr.isometricGL_of_unimodular_of_isometricIn`, O'Meara 92:2), which gives $g \in O(V)(F_\mathfrak p)$ with $gM_\mathfrak p = M'_\mathfrak p$
  (`exists_locAct_of_isometricGL`).
-/
import QuadFormsKB.Lattices.NeighborLocal
import QuadFormsKB.HilbertModular.HeckeGenus

open Matrix NumberField IsDedekindDomain
open scoped Pointwise

set_option linter.unusedSectionVars false

attribute [local instance] Ideal.Quotient.field

namespace QuadFormsKB.HilbertModular

open QuadFormsKB.Lattices QuadFormsKB.Lattices.Nbr QuadFormsKB.LocalDensity

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-! ### Evaluation of Gram forms over a completion -/

section Completion

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- $(Q_\gamma \otimes \mathfrak o_v)(y) = Q(\gamma y)$ for all $y \in F_v^n$. -/
theorem evalIn_gramZ_map_completion (Q : QuadForm F n) (γ : GL (Fin n) F) (h : IsIntegral Q (latOf γ))
    (y : Fin n → Fv) :
    ((gramZ Q γ h).map (algebraMap (𝓞 F) 𝔬)).evalIn Fv y = Q.evalIn Fv (γ.val.map (algebraMap F Fv) *ᵥ y) := by
  refine evalIn_eq_of_evalIn_o v (A := fun y => ((gramZ Q γ h).map (algebraMap (𝓞 F) 𝔬)).evalIn Fv y)
    (B := fun y => Q.evalIn Fv (γ.val.map (algebraMap F Fv) *ᵥ y)) (fun c y => ?_) (fun c y => ?_)
    (fun x => ?_) y
  · exact Nbr.qv_smul y c
  · simp only [mulVec_smul, evalIn_smul']
  · rw [← coe_eval_gramZ_map]
    exact Nbr.qv_map (S := 𝔬) (T := Fv) (Q := (gramZ Q γ h).map (algebraMap (𝓞 F) 𝔬)) x

/-- **The local isometry from an isometry of Gram forms** at one place (the per-place step of `sameGenus_latOf_iff`): if
$Q_\gamma \cong Q_\delta$ over $\mathfrak o_v$ then $gM_v = M'_v$ for some $g \in O(V)(F_v)$, $M = \gamma\mathcal O_F^n$, $M' = \delta\mathcal O_F^n$. -/
theorem exists_locAct_of_isometricGL (Q : QuadForm F n) (γ δ : GL (Fin n) F) (hγ : IsIntegral Q (latOf γ))
    (hδ : IsIntegral Q (latOf δ))
    (hiso : Siegel.IsometricGL ((gramZ Q γ hγ).map (algebraMap (𝓞 F) 𝔬))
      ((gramZ Q δ hδ).map (algebraMap (𝓞 F) 𝔬))) :
    ∃ g ∈ orthGroup Q Fv, locAct v g (loc v (latOf γ)) = loc v (latOf δ) := by
  have hloc : ∀ (ε : GL (Fin n) F),
      loc v (latOf ε) = locAct v (GeneralLinearGroup.map (algebraMap F Fv) ε) (std v) :=
    fun ε => by rw [latOf, loc_glImage, loc_intVec]
  obtain ⟨P₀, hP₀⟩ := hiso
  set γv := GeneralLinearGroup.map (algebraMap F Fv) γ
  set δv := GeneralLinearGroup.map (algebraMap F Fv) δ
  set P := GeneralLinearGroup.map (algebraMap 𝔬 Fv) P₀
  have hval : ∀ y, Q.evalIn _ (γv.val *ᵥ (P.val *ᵥ y)) = Q.evalIn _ (δv.val *ᵥ y) := by
    refine evalIn_eq_of_evalIn_o v (A := fun y => Q.evalIn _ (γv.val *ᵥ (P.val *ᵥ y)))
      (B := fun y => Q.evalIn _ (δv.val *ᵥ y)) (fun c y => ?_) (fun c y => ?_) (fun x => ?_)
    · simp only [mulVec_smul, evalIn_smul']
    · simp only [mulVec_smul, evalIn_smul']
    · have h1 := congrArg (fun t : 𝔬 => (t : Fv)) (hP₀ x)
      rw [coe_eval_gramZ_map, coe_eval_gramZ_map] at h1
      have e : (P.val *ᵥ fun i => ((x i : 𝔬) : Fv)) =
          fun i => (((P₀.val *ᵥ x) i : 𝔬) : Fv) := by
        funext i; exact (RingHom.map_mulVec (algebraMap _ Fv) P₀.val x i).symm
      change Q.evalIn _ (γ.val.map (algebraMap F _) *ᵥ (P.val *ᵥ _)) =
        Q.evalIn _ (δ.val.map (algebraMap F _) *ᵥ _)
      rw [e]; exact h1
  refine ⟨δv * P⁻¹ * γv⁻¹, mem_orthGroup_of_evalIn Q fun z => ?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, ← hval, mulVec_inv_mulVec,
      mulVec_inv_mulVec]
  · rw [hloc, hloc, ← locAct_mul, mul_assoc, mul_assoc, inv_mul_cancel, mul_one, locAct_mul,
      show P⁻¹ = GeneralLinearGroup.map (algebraMap _ Fv) P₀⁻¹ from (map_inv _ _).symm,
      locAct_map_std]

end Completion

/-! ### The Gram form of $L(\vec v)$ is unimodular at $\pi$ -/

section Unimodular

/-- Evaluating $Q_0 \otimes F$ is evaluating $Q_0$. -/
lemma qv_formF (Q₀ : QuadForm (𝓞 F) n) (x : Fin n → F) : Nbr.qv F (formF Q₀) x = Nbr.qv F Q₀ x := by
  simp [qv, QuadForm.evalIn, QuadForm.map]

/-- **Polarization:** $\bar B(x, y) = \bar Q(x + y) - \bar Q(x) - \bar Q(y)$. -/
lemma bv_eq_polar {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (Q : QuadForm R n)
    (x y : Fin n → S) : bv S Q x y = Nbr.qv S Q (x + y) - Nbr.qv S Q x - Nbr.qv S Q y := by
  have := qv_add_smul (S := S) (Q := Q) x y 1
  rw [one_smul, one_mul, one_pow, one_mul] at this
  rw [this]; ring

/-- $B_{Q_\gamma}(a, b) = B_Q(\gamma a, \gamma b)$. -/
lemma bv_gramZ (Q₀ : QuadForm (𝓞 F) n) (δ : GL (Fin n) F) (h : IsIntegral (formF Q₀) (latOf δ))
    (a b : Fin n → F) :
    bv F (gramZ (formF Q₀) δ h) a b = bv F Q₀ (δ.val *ᵥ a) (δ.val *ᵥ b) := by
  rw [bv_eq_polar, bv_eq_polar, qv_gramZ, qv_gramZ, qv_gramZ, mulVec_add, ← qv_formF, ← qv_formF,
    ← qv_formF]

variable {π : 𝓞 F} (hπ : Prime π)
include hπ

/-- **The Gram form of the neighbour $L(\vec v) = \delta\mathcal O_F^n$ is unimodular at $\pi$** ($\pi \nmid \det H(Q_0)$). *Proof:* if
$\bar G\bar c = 0$ with $\bar c \ne 0$, then $x = \delta c \in L(\vec v)$ has $B(x, L(\vec v)) \subseteq \pi\mathcal O_F$, so $x \in \pi L(\vec v)$
(`Nbr.eq_smul_of_bv_dvd`), i.e. $\pi \mid c$. -/
theorem not_dvd_det_gramZ_nbLat (Q₀ : QuadForm (𝓞 F) n) (hdet : ¬ π ∣ Q₀.hessian.det) {v : Fin n → 𝓞 F}
    (hv : π ^ 2 ∣ Nbr.qv (𝓞 F) Q₀ v) (hv0 : red π v ≠ 0) (δ : GL (Fin n) F)
    (hδ : latOf δ = nbLat (K := F) Q₀ π v) (h : IsIntegral (formF Q₀) (latOf δ)) :
    ¬ π ∣ (gramZ (formF Q₀) δ h).hessian.det := by
  classical
  have := isMaximal_span hπ
  have := finite_res hπ
  letI := Fintype.ofFinite (Res π)
  set G := gramZ (formF Q₀) δ h
  intro hd
  have hdet0 : (G.hessian.map (algebraMap (𝓞 F) (Res π))).det = 0 := by
    rw [show (G.hessian.map (algebraMap (𝓞 F) (Res π))).det = algebraMap (𝓞 F) (Res π) G.hessian.det from
      (RingHom.map_det _ _).symm]
    exact (dvd_of_red _).mpr hd
  obtain ⟨cb, hcb0, hcb⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
  set c := liftRes (π := π) cb
  have hc : red π c = cb := red_liftRes cb
  set x := δ.val *ᵥ cv F c
  have hcL : cv F c ∈ (intVec : Submodule (𝓞 F) (Fin n → F)) := by
    rw [intVec_eq_stdLat]; exact cv_mem_stdLat c
  have hx : x ∈ nbLat (K := F) Q₀ π v := by rw [← hδ]; exact mulVec_mem_glImage hcL
  have hB : ∀ z ∈ nbLat (K := F) Q₀ π v, ∃ b : 𝓞 F, π ∣ b ∧ bv F Q₀ x z = algebraMap (𝓞 F) F b := by
    intro z hz
    rw [← hδ] at hz
    obtain ⟨w, hw, rfl⟩ := mem_glImage.mp hz
    rw [intVec_eq_stdLat] at hw
    obtain ⟨w', rfl⟩ := hw
    refine ⟨bv (𝓞 F) G c w', ?_, ?_⟩
    · rw [← dvd_of_red, ← bv_red, hc, bv_comm]
      simp only [bv]
      rw [show G.hessian.map (algebraMap (𝓞 F) (Res π)) *ᵥ cb = 0 from hcb, dotProduct_zero]
    · rw [← bv_gramZ Q₀ δ h, bv_cv]
  obtain ⟨x', hx', hxx'⟩ := eq_smul_of_bv_dvd (K := F) hπ hdet hv hv0 hx hB
  rw [← hδ] at hx'
  obtain ⟨w, hw, rfl⟩ := mem_glImage.mp hx'
  rw [intVec_eq_stdLat] at hw
  obtain ⟨c'', rfl⟩ := hw
  have e : cv F c = cv F (π • c'') := by
    apply mulVec_injective_gl δ
    show δ.val *ᵥ cv F c = δ.val *ᵥ cv F (π • c'')
    simp only [x] at hxx'
    rw [hxx', cv_smul, mulVec_smul]
  have : c = π • c'' := cv_injective e
  apply hcb0
  rw [← hc, this, red_smul, (dvd_of_red (π := π) π).mpr (dvd_refl π), zero_smul]

/-- **Away from $\pi$ the neighbour is locally the standard lattice:** $L(\vec v)_\mathfrak q = \mathfrak o_\mathfrak q^n$ for $\mathfrak q \ne (\pi)$. -/
theorem loc_nbLat_of_ne (Q₀ : QuadForm (𝓞 F) n) {v : Fin n → 𝓞 F} (hv : π ^ 2 ∣ Nbr.qv (𝓞 F) Q₀ v)
    (w : HeightOneSpectrum (𝓞 F)) (hw : w ≠ hosOf hπ) :
    loc w (nbLat (K := F) Q₀ π v) = loc w (intVec : Submodule (𝓞 F) (Fin n → F)) := by
  have hπw : π ∉ w.asIdeal := by
    intro hm
    apply hw
    have h1 : Ideal.span {π} ≤ w.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr hm
    have h2 := (isMaximal_span hπ).eq_of_le w.isPrime.ne_top h1
    exact HeightOneSpectrum.ext h2.symm
  set u := algebraMap (𝓞 F) (w.adicCompletionIntegers F) π
  have hu : IsUnit u := by
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    change Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) π) = 1
    rw [valued_algebraMap_int, HeightOneSpectrum.intValuation_eq_one_iff]; exact hπw
  have key : ∀ (A B : Submodule (𝓞 F) (Fin n → F)), (∀ x ∈ A, π • x ∈ B) → loc w A ≤ loc w B := by
    intro A B hAB
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    have h1 := locVec_mem_loc w (hAB x hx)
    rw [locVec_smul_int] at h1
    have := (loc w B).smul_mem (↑hu.unit⁻¹) h1
    rwa [smul_smul, IsUnit.val_inv_mul, one_smul] at this
  refine le_antisymm (key _ _ fun x hx => ?_) (key _ _ fun x hx => ?_)
  · obtain ⟨y, rfl⟩ := exists_eq_of_mem_nbLat hπ hx
    rw [algebra_compatible_smul F π, smul_smul, mul_inv_cancel₀ (πK_ne_zero hπ), one_smul,
      intVec_eq_stdLat]
    exact cv_mem_stdLat y
  · rw [intVec_eq_stdLat] at hx
    obtain ⟨y, rfl⟩ := hx
    rw [algebra_compatible_smul F π, ← cv_smul]
    exact smul_cv_mem_nbLat hπ hv y

end Unimodular

/-! ### Neighbours stay in the genus -/

section Genus

variable [IsTotallyReal F] [IsPrincipalIdealRing (𝓞 F)]

/-- **A neighbour of a free lattice is in its genus** ($\mathcal O_F$ a PID, $\pi \nmid 2\det H(Q_\gamma)$): for $M = \gamma\mathcal O_F^n$ integral
with Gram form $Q_\gamma$ and $N = L(\vec v)$ the explicit $\pi$-neighbour of $\mathcal O_F^n$ for $Q_\gamma$, $\gamma N$ is in the genus of $M$. -/
@[kb "kneser1957" "Satz 1 (the neighbour lies in the genus), over F [unverified]"]
theorem sameGenus_glImage_nbLat (Q : QuadForm F n) (γ : GL (Fin n) F) (hγ : IsIntegral Q (latOf γ))
    {π : 𝓞 F} (hπ : Prime π) (h2 : ¬ π ∣ 2) (hdet : ¬ π ∣ (gramZ Q γ hγ).hessian.det)
    {v : Fin n → 𝓞 F} (hv : π ^ 2 ∣ Nbr.qv (𝓞 F) (gramZ Q γ hγ) v) (hv0 : red π v ≠ 0) :
    SameGenus Q (latOf γ) (glImage γ (nbLat (K := F) (gramZ Q γ hγ) π v)) := by
  classical
  set Q' := gramZ Q γ hγ
  set N := nbLat (K := F) Q' π v
  have h0 := πK_ne_zero (K := F) hπ
  -- `N` is a lattice, hence free
  have hNlat : N.IsLattice F := by
    have hstd : (intVec : Submodule (𝓞 F) (Fin n → F)).IsLattice F := intVec_isLattice
    set u : Fˣ := Units.mk0 _ h0
    have h1 : u • (intVec : Submodule (𝓞 F) (Fin n → F)) ≤ N := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.mp hx
      rw [intVec_eq_stdLat] at hy
      obtain ⟨z, rfl⟩ := hy
      show (algebraMap (𝓞 F) F π) • cv F z ∈ N
      rw [← cv_smul]; exact smul_cv_mem_nbLat hπ hv z
    have h2' : N ≤ u⁻¹ • (intVec : Submodule (𝓞 F) (Fin n → F)) := by
      intro x hx
      obtain ⟨y, rfl⟩ := exists_eq_of_mem_nbLat hπ hx
      refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨cv F y, ?_, rfl⟩
      rw [intVec_eq_stdLat]; exact cv_mem_stdLat y
    haveI := hstd
    exact Submodule.IsLattice.of_le_of_isLattice_of_fg F h1
      (Submodule.FG.of_le (Submodule.IsLattice.fg (A := F) (M := u⁻¹ • intVec)) h2')
  obtain ⟨δ, hδ⟩ := exists_latOf_of_isPrincipalIdealRing (n := n) ⟨N, hNlat⟩
  simp only at hδ
  -- integrality
  have hNint : IsIntegral (formF Q') (latOf δ) := by
    intro x hx
    rw [← hδ] at hx
    obtain ⟨z, hz⟩ := nbLat_integral hπ hv x hx
    rw [← qv_formF] at hz
    exact ⟨z, hz.symm⟩
  have hM' : glImage γ N = latOf (γ * δ) := by rw [latOf, glImage_mul, ← latOf, ← hδ]
  have hint' : IsIntegral Q (latOf (γ * δ)) := by
    rw [← hM']
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_glImage.mp hx
    obtain ⟨z, hz⟩ := nbLat_integral hπ hv y hy
    exact ⟨z, by rw [← qv_gramZ γ hγ]; exact hz.symm⟩
  rw [hM']
  intro w
  by_cases hw : w = hosOf hπ
  · -- at `π`: classification of unimodular forms
    subst hw
    apply exists_locAct_of_isometricGL (hosOf hπ) Q γ (γ * δ) hγ hint'
    have hπw := NF.irreducible_π (hosOf hπ)
    have h2w := NF.π_not_dvd_two (hosOf hπ) (two_not_mem hπ h2)
    -- the Gram form of `γδ` is that of `δ` for `Q'`
    have hG : gramZ Q (γ * δ) hint' = gramZ (formF Q') δ hNint := by
      refine QuadForm.ext_eval fun x => algebraMap_O_injective ?_
      rw [algebraMap_eval_gramZ, algebraMap_eval_gramZ, Units.val_mul, ← mulVec_mulVec]
      rw [show (formF Q').eval (δ.val *ᵥ intCoe x) = Nbr.qv F Q' (δ.val *ᵥ intCoe x) from qv_formF _ _,
        qv_gramZ]
    have hdet' : ¬ π ∣ (gramZ Q (γ * δ) hint').hessian.det := by
      rw [hG]; exact not_dvd_det_gramZ_nbLat hπ Q' hdet hv hv0 δ hδ.symm hNint
    refine isometricGL_of_unimodular_of_isometricIn hπw h2w ((hosOf hπ).adicCompletion F) _ _
      (by rw [NF.det_hessian_Qp, NF.π_dvd_ι_iff, hosOf_asIdeal, Ideal.mem_span_singleton]; exact hdet)
      (by rw [NF.det_hessian_Qp, NF.π_dvd_ι_iff, hosOf_asIdeal, Ideal.mem_span_singleton]; exact hdet')
      (GeneralLinearGroup.map (algebraMap F _) δ) fun x => ?_
    rw [evalIn_gramZ_map_completion, evalIn_gramZ_map_completion]
    change _ = Q.evalIn _ (γ.val.map _ *ᵥ (δ.val.map _ *ᵥ x))
    rw [mulVec_mulVec, ← Matrix.map_mul, Units.val_mul]
  · -- away from `π`: the localizations agree
    refine ⟨1, (orthGroup Q _).one_mem, ?_⟩
    rw [locAct_one, latOf, latOf, glImage_mul, loc_glImage, loc_glImage, ← latOf, ← hδ,
      loc_nbLat_of_ne hπ Q' hv w hw]

/-- **Kneser neighbours stay in the genus over $\mathcal O_F$** ($\mathcal O_F$ a PID, $\pi \nmid 2\det H(Q_0)$; Kneser 1957, Satz 1
[unverified]): discharges `NbrInGenus Q₀ π`. -/
@[kb "kneser1957" "Satz 1 (neighbours lie in the genus), over F, O_F a PID [unverified]"]
theorem nbrInGenus_of_pid (Q₀ : QuadForm (𝓞 F) n) {π : 𝓞 F} (hπ : Prime π) (h2 : ¬ π ∣ 2)
    (hdet : ¬ π ∣ Q₀.hessian.det) : NbrInGenus Q₀ π := by
  classical
  intro M M' hl hg hN
  have := finite_res hπ
  let _ := Fintype.ofFinite (Res π)
  obtain ⟨γ, hγ⟩ := exists_latOf_of_isPrincipalIdealRing (n := n) ⟨M, hl⟩
  simp only at hγ
  subst hγ
  have hi : IsIntegral (formF Q₀) (latOf γ) := hN.int_left
  have hfs := formSameGenus_gramZ Q₀ hg hi
  have hdet' := not_dvd_det_of_formSameGenus hπ hfs hdet
  have hS := setOf_isNbrL_latOf (Q := formF Q₀) hπ γ hi hdet'
  have hmem : M' ∈ {M' | IsNbrL (formF Q₀) π (latOf γ) M'} := hN
  rw [hS] at hmem
  obtain ⟨N, hN', rfl⟩ := hmem
  unfold neighbors at hN'
  obtain ⟨vb, hvb, rfl⟩ := Finset.mem_image.mp hN'
  have := isMaximal_span hπ
  obtain ⟨h1, h2'⟩ := liftV_spec hπ hdet' hvb
  exact hg.trans _ (sameGenus_glImage_nbLat (formF Q₀) γ hi hπ h2 hdet' h2'
    (by rw [h1]; exact (mem_isoSet.mp hvb).1))

/-- **The $T(\pi^2)$ relation for the genus representation numbers, unconditionally** ($\mathcal O_F$ a PID, $Q_0$ totally positive definite of
even rank $n \ge 2$, $\pi \nmid 2\det H(Q_0)$, $\pi \nmid \nu$): `genus_sum_latRepF_sq` with `NbrInGenus` discharged by `nbrInGenus_of_pid`. -/
@[kb "eichler1952" "T(𝔭²) relation for the genus average, over F, unconditional [unverified]"]
theorem genus_sum_latRepF_sq_of_pid {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) {π : 𝓞 F}
    (hπ : Prime π) (h2 : ¬ π ∣ 2) (hdet : ¬ π ∣ Q₀.hessian.det) (hn : Even n) (hn2 : 2 ≤ n) {ν : 𝓞 F}
    (hν : ¬ π ∣ ν) :
    ∑ c ∈ (genusClasses_finite hQ stdLat (isIntegral_stdLat Q₀)).toFinset,
        ((LatClass.autCard (formF Q₀) c : ℂ))⁻¹ * (latRepF (formF Q₀) c.out.1 (π ^ 2 * ν) : ℂ) =
      heckeEigen Q₀ hπ * ∑ c ∈ (genusClasses_finite hQ stdLat (isIntegral_stdLat Q₀)).toFinset,
        ((LatClass.autCard (formF Q₀) c : ℂ))⁻¹ * (latRepF (formF Q₀) c.out.1 ν : ℂ) :=
  genus_sum_latRepF_sq hQ hπ h2 hdet (nbrInGenus_of_pid Q₀ hπ h2 hdet) hn hn2 hν

end Genus

end QuadFormsKB.HilbertModular
