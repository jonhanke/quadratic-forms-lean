/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.IdealScale
import QuadFormsKB.HilbertModular.SteinitzGenus

/-!
# the orbital Euler product over every number field: the sum over all ideals

`OrbitalEuler` proved the orbital Euler product (`orbitalEulerProduct`) for $\mathcal O_F$ a PID: its per-ideal step wrote each fractional ideal as
$\mathfrak b = (\beta)$. Here the per-ideal step is proved for **every** fractional ideal $\mathfrak b$, so the Euler product, $\tau(SO) = 2$
by Weil's induction (`tamagawaNumberTwo_of_complement_nf`) and the mass formula hold for every totally real $F$ (any class number).

*Per-ideal step* (`finsum_sphereCount_eq_nf`): choose $\beta \in \mathfrak b\setminus0$ and $e = \mathrm{ord}(\beta) - \mathrm{ord}(\mathfrak b) \ge 0$. Then
$\eta \mapsto \beta\gamma\eta$ identifies the vectors of $\mathfrak b^{-1}M$ of norm $\rho$ with the vectors of the **non-free** integral lattice
$\varpi^eM \subseteq M$ of norm $\beta^2\rho$ (`sphereCount_eq_repCount_scale`); the genus of $\varpi^e\mathcal O_F^{n+1}$ is the image of the
genus of $\mathcal O_F^{n+1}$ (`repMass_scaleLat`); the factorization of the Siegel formula applies to the lattice $\varpi^e\mathcal O_F^{n+1}$
(`repMass_eq_mass_mul_finprod_lat`); and locally $W(\varpi^k\Lambda, \varpi^kc) = W(\Lambda, c)$ (`locTypeSumG_scale`) returns the local factor
$W_\mathfrak p(\mathrm{ord}_\mathfrak p\mathfrak b)$. `GenusFree` comes from Steinitz (`genusFree_formF`).
-/

open NumberField Matrix MulAction Filter Topology
open scoped Real ENNReal nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

open Lattices LocalDensity QuadForm IsDedekindDomain
open QuadFormsKB.HilbertModular QuadFormsKB.IdeleClass QuadFormsKB.AdditiveZeta QuadFormsKB.SphericalUnfold

/-! ### Local types under scaling -/

section LocalScale

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (m : F) (Q' : QuadForm F n)

local notation "Fv" => v.adicCompletion F

/-- $M \mapsto \varpi^kM$: $Y_\mathfrak p(\Lambda, c) \simeq Y_\mathfrak p(\varpi^k\Lambda, \varpi^kc)$, equivariantly ($\varpi^k$ is central). -/
def scaleEquiv (k : ℤ) (Λ : Submodule (v.adicCompletionIntegers F) (Fin (n + 1) → Fv)) (c : Fv) :
    LocCompSetG v m Q' Λ c ≃ LocCompSetG v m Q' (locAct v (scalGL v k) Λ) (unifV v ^ k * c) where
  toFun M := ⟨locAct v (scalGL v k) M.1, by
      obtain ⟨g, hg⟩ := M.2.1
      exact ⟨g, by rw [← locAct_mul, ← scalGL_comm, locAct_mul, hg]⟩,
    ⟨c • e₀, M.2.2, by show (scalGL v k).val *ᵥ (c • e₀) = _; rw [scalGL_mulVec, smul_smul]⟩⟩
  invFun M := ⟨locAct v (scalGL v (-k)) M.1, by
      obtain ⟨g, hg⟩ := M.2.1
      refine ⟨g, ?_⟩
      rw [← hg, ← locAct_mul, ← locAct_mul]
      congr 1
      rw [scalGL_comm v (-k), mul_assoc, ← scalGL_add, neg_add_cancel, scalGL_zero, mul_one],
    ⟨(unifV v ^ k * c) • e₀, M.2.2, by
      show (scalGL v (-k)).val *ᵥ ((unifV v ^ k * c) • e₀) = _
      rw [scalGL_mulVec, smul_smul, ← mul_assoc, ← zpow_add₀ (unifV_ne_zero v), neg_add_cancel, zpow_zero, one_mul]⟩⟩
  left_inv M := Subtype.ext (by
    show locAct v (scalGL v (-k)) (locAct v (scalGL v k) M.1) = M.1
    rw [← locAct_mul, ← scalGL_add, neg_add_cancel, scalGL_zero, locAct_one])
  right_inv M := Subtype.ext (by
    show locAct v (scalGL v k) (locAct v (scalGL v (-k)) M.1) = M.1
    rw [← locAct_mul, ← scalGL_add, add_neg_cancel, scalGL_zero, locAct_one])

/-- **Scaling invariance of local type sums**: $W_\mathfrak p(\varpi^k\Lambda, \varpi^kc) = W_\mathfrak p(\Lambda, c)$. -/
theorem locTypeSumG_scale (hQ' : Q'.Nondegenerate) (k : ℤ) {Λ : Submodule (v.adicCompletionIntegers F) (Fin (n + 1) → Fv)}
    (hΛ : Λ.IsLattice Fv) (c : Fv) :
    locTypeSumG v m Q' (locAct v (scalGL v k) Λ) (unifV v ^ k * c) = locTypeSumG v m Q' Λ c :=
  (locTypeSumG_congr v m Q' hQ' hΛ (scaleEquiv v m Q' k Λ c) fun h M => Subtype.ext (by
    show locAct v (scalGL v k) (locAct v (orthEmb m Q' Fv h : GL (Fin (n + 1)) Fv) M.1) =
      locAct v (orthEmb m Q' Fv h : GL (Fin (n + 1)) Fv) (locAct v (scalGL v k) M.1)
    rw [← locAct_mul, ← locAct_mul, scalGL_comm])).symm

end LocalScale

/-! ### The per-ideal identity for a general lattice -/

section PerIdealLat

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

/-- **The per-ideal factorization for any integral lattice $L$** (not only $\mathcal O_F^{n+1}$; Weil 1982, §4.5, p. 109; §3.4–3.5 [unverified locator]):
$$\mathrm{repMass}(L, \beta^2\rho) = \mathrm{Mass}(Q_0')\prod_\mathfrak pW_\mathfrak p(g^{-1}L_\mathfrak p, \beta).$$
The proof is `repMass_eq_mass_mul_finprod` with $L$ in place of $\mathcal O_F^{n+1}$. -/
@[kb "weil1982" "§4.5, p. 109 (orbit counting in coordinates adapted to ξ_ρ); §3.4-3.5 [unverified locator]"]
theorem repMass_eq_mass_mul_finprod_lat (Q₀ : QuadForm (𝓞 F) (n + 1)) (hpd : IsTotallyPosDef (formF Q₀))
    {ρ : F} (hρ : ρ ≠ 0) (fr : AdaptedFrame (formF Q₀) ρ) {β : F} (hβ : β ≠ 0) (L : Lat F (n + 1))
    (hLi₀ : Lattices.IsIntegral (formF Q₀) L.1) :
    repMass (formF Q₀) L (β ^ 2 * ρ) =
      mass (fr.Q'.map (algebraMap (𝓞 F) F)) (stdLat F n) *
        ∏ᶠ v : HeightOneSpectrum (𝓞 F),
          locTypeSumG v ρ (fr.Q'.map (algebraMap (𝓞 F) F)) (loc v (glImage fr.g⁻¹ L.1)) (algebraMap F (v.adicCompletion F) β) := by
  classical
  set QF' := fr.Q'.map (algebraMap (𝓞 F) F)
  set gb : GL (Fin (n + 1)) F := fr.g * diagGl hβ
  set m := β ^ 2 * ρ
  have hm : m ≠ 0 := mul_ne_zero (pow_ne_zero 2 hβ) hρ
  have hQF : (formF Q₀).Nondegenerate := hpd.nondegenerate
  have hQ'nd : fr.Q'.Nondegenerate := fr.nondegenerate hQF hρ
  have hQF' : QF'.Nondegenerate := by
    rw [QuadForm.Nondegenerate, hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hQ'nd
  have hcomp : (formF Q₀).compMat gb.val = splitForm m QF' := by
    rw [show gb.val = fr.g.val * cornerMat β 1 from rfl, ← compMat_mul, fr.compMat_eq,
      splitForm_compMat_cornerMat]
  set Λ := Lat.image gb⁻¹ L
  have hpd_s : IsTotallyPosDef (splitForm m QF') := hcomp ▸ isTotallyPosDef_compMat (formF Q₀) gb hpd
  have hLi_s : Lattices.IsIntegral (splitForm m QF') Λ.1 := hcomp ▸ isIntegral_compMat (formF Q₀) gb hLi₀
  have hLi' : Lattices.IsIntegral QF' (stdLat F n).1 := HilbertModular.isIntegral_stdLat fr.Q'
  have hpd' := isTotallyPosDef_of_splitForm hpd_s
  rw [← repMass_compMat (formF Q₀) gb hpd hLi₀ m, hcomp, repMass_eq_mass_mul m QF' Λ hpd_s hLi_s hm hpd' hLi',
    typeSum_eq_prodG m fr.Q' Λ hm hQ'nd hpd_s hLi_s hLi']
  congr 1
  -- the local factors in the frame coordinates
  set T : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    locTypeSumG v ρ QF' (loc v (glImage fr.g⁻¹ L.1)) (algebraMap F (v.adicCompletion F) β)
  have hβv : ∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (v.adicCompletion F) β ≠ 0 :=
    fun v => (map_ne_zero _).mpr hβ
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F),
      locTypeSumG v m QF' (loc v Λ.1) 1 = T v := by
    intro v
    have hΛ : (loc v Λ.1).IsLattice (v.adicCompletion F) := loc_isLattice v Λ.2
    rw [locTypeSumG_transport v QF' hQF' ρ (hβv v) (by simp only [m, map_mul, map_pow]; ring) hΛ 1, mul_one]
    congr 1
    show locAct v (diagD v (hβv v)) (loc v (glImage gb⁻¹ L.1)) = loc v (glImage fr.g⁻¹ L.1)
    rw [loc_glImage, loc_glImage, ← locAct_mul, show gb⁻¹ = (diagGl hβ)⁻¹ * fr.g⁻¹ by
      simp [gb, _root_.mul_inv_rev], map_mul, map_inv, map_diagGl v hβ (hβv v), ← mul_assoc, mul_inv_cancel, one_mul]
  have hone : ∀ v ∉ badSetG m Λ hm, T v = 1 := by
    intro v hv
    obtain ⟨hL, hmv, h2v⟩ := not_mem_badSetG m Λ hm hv
    rw [← hloc v, hL]
    have hmv' : Valued.v (algebraMap F (v.adicCompletion F) m) ≤ 1 := by rw [valued_algebraMap, hmv]
    set mo := toO v _ hmv'
    have hmo : ((mo : v.adicCompletionIntegers F) : v.adicCompletion F) = algebraMap F _ m := rfl
    have hQo' : IsIntModel v QF' (NF.Qp v fr.Q') := fun y => evalIn_coe_o v fr.Q' y
    have hunit : ∀ x : v.adicCompletionIntegers F, Valued.v (x : v.adicCompletion F) = 1 → IsUnit x := by
      intro x hx
      rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
      exact hx
    have h2u : IsUnit (2 : v.adicCompletionIntegers F) := by
      apply hunit
      have : ((2 : v.adicCompletionIntegers F) : v.adicCompletion F) = algebraMap F _ 2 := by
        rw [map_ofNat]; rfl
      rw [this, valued_algebraMap, h2v]
    have hmu : IsUnit mo := hunit mo (by rw [hmo, valued_algebraMap, hmv])
    have h4 : IsUnit (4 * mo) := by
      rw [show (4 : v.adicCompletionIntegers F) = 2 * 2 by norm_num]
      exact (h2u.mul h2u).mul hmu
    have hnd : (splitForm mo (NF.Qp v fr.Q')).Nondegenerate := by
      rw [QuadForm.Nondegenerate, det_hessian_splitForm]
      exact mul_ne_zero (mul_ne_zero (NF.two_ne_zero' v) hmu.ne_zero) (NF.nondegenerate_Qp v hQ'nd)
    exact locTypeSumG_std_eq_one v m QF' hQF' hQo' hmo h4 hnd
  rw [Finset.prod_congr rfl fun v _ => hloc v]
  exact (finprod_eq_prod_of_mulSupport_subset T fun v hv => by
    by_contra h; exact hv (hone v h)).symm

end PerIdealLat

/-! ### Sphere counts for a non-principal ideal -/

section Bridge

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

open FractionalIdeal

theorem exp_mul_le_iff (a b : ℤ) (x : WithZero (Multiplicative ℤ)) :
    WithZero.exp a * x ≤ WithZero.exp a * WithZero.exp b ↔ x ≤ WithZero.exp b :=
  mul_le_mul_iff_right₀ (zero_lt_iff.mpr WithZero.exp_ne_zero)

/-- **Membership in the scaled lattice**: for $M = \gamma\mathcal O_F^N$, $\beta \in F^\times$ and $e_\mathfrak p = \mathrm{ord}_\mathfrak p\beta - \mathrm{ord}_\mathfrak p\mathfrak b$,
$\gamma(\beta\eta) \in \varpi^eM$ iff every coordinate of $\eta$ lies in $\mathfrak b^{-1}$. -/
theorem mem_scaleLat_latOf_iff (γ : GL (Fin N) F) (hM : (Lattices.latOf γ).IsLattice F) (𝔟 : FracIdeal F) {β : F} (hβ : β ≠ 0)
    (e : HeightOneSpectrum (𝓞 F) → ℤ) (he : ∀ᶠ v in Filter.cofinite, e v = 0)
    (hev : ∀ v, e v = count F v (spanSingleton (𝓞 F)⁰ β) - count F v (𝔟 : FractionalIdeal (𝓞 F)⁰ F))
    (η : Fin N → F) :
    γ.val *ᵥ (β • η) ∈ (scaleLat e he ⟨Lattices.latOf γ, hM⟩).1 ↔ ∀ i, η i ∈ ((𝔟 : FractionalIdeal (𝓞 F)⁰ F))⁻¹ := by
  have h𝔟 : (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := 𝔟.ne_zero
  have h𝔟i : ((𝔟 : FractionalIdeal (𝓞 F)⁰ F))⁻¹ ≠ 0 := inv_ne_zero h𝔟
  rw [mem_scaleLat]
  simp only [Analysis.mem_iff_forall_valuation_le h𝔟i, count_inv]
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), locVec v (γ.val *ᵥ (β • η)) ∈
      locAct v (scalGL v (e v)) (loc v (Lattices.latOf γ)) ↔ locVec v (β • η) ∈ ball v (e v) := by
    intro v
    rw [Lattices.latOf, loc_glImage, loc_intVec, ← locAct_mul, scalGL_comm, locAct_mul, locAct_scalGL_std,
      locVec_mulVec, mem_locAct]
    constructor
    · rintro ⟨z, hz, hzx⟩
      set G := Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) γ
      have hzx' : G.val *ᵥ z = G.val *ᵥ locVec v (β • η) := hzx
      have := congrArg (fun y => (G⁻¹).val *ᵥ y) hzx'
      simp only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec] at this
      rwa [← this]
    · intro h; exact ⟨_, h, rfl⟩
  simp only [hloc]
  constructor
  · intro h i v
    have := h v i
    rw [locVec_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_mul, valued_algebraMap, valued_algebraMap,
      Analysis.valuation_eq_exp_neg_count v hβ, hev v,
      show -(count F v (spanSingleton (𝓞 F)⁰ β) - count F v (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) =
        -count F v (spanSingleton (𝓞 F)⁰ β) + count F v (𝔟 : FractionalIdeal (𝓞 F)⁰ F) by ring,
      WithZero.exp_add, exp_mul_le_iff] at this
    rwa [neg_neg]
  · intro h v i
    have := h i v
    rw [neg_neg] at this
    rw [locVec_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_mul, valued_algebraMap, valued_algebraMap,
      Analysis.valuation_eq_exp_neg_count v hβ, hev v,
      show -(count F v (spanSingleton (𝓞 F)⁰ β) - count F v (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) =
        -count F v (spanSingleton (𝓞 F)⁰ β) + count F v (𝔟 : FractionalIdeal (𝓞 F)⁰ F) by ring,
      WithZero.exp_add, exp_mul_le_iff]
    exact this

variable [IsTotallyReal F]

open QuadFormsKB.SphericalFibration in
/-- **Sphere counts for any fractional ideal are representation numbers of a non-free lattice**: with $c.\mathrm{out} = \gamma\mathcal O_F^N$,
$\beta \in F^\times$ and $e = \mathrm{ord}(\beta) - \mathrm{ord}(\mathfrak b)$, $\eta \mapsto \gamma\beta\eta$ is a bijection
$\{\eta \in \mathfrak b^{-1}\mathcal O_F^N : Q_\gamma(\eta) = \rho\} \to \{w \in \varpi^e\,c.\mathrm{out} : Q(w) = \beta^2\rho\}$. -/
theorem sphereCount_eq_repCount_scale (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀))
    (hfree : GenusFree (formF Q₀) (stdLat F N)) {c : LatClass (formF Q₀)} (hc : c ∈ genusClasses (formF Q₀) (stdLat F N))
    (𝔟 : FracIdeal F) {β : F} (hβ : β ≠ 0) (e : HeightOneSpectrum (𝓞 F) → ℤ) (he : ∀ᶠ v in Filter.cofinite, e v = 0)
    (hev : ∀ v, e v = count F v (spanSingleton (𝓞 F)⁰ β) - count F v (𝔟 : FractionalIdeal (𝓞 F)⁰ F))
    (hpos : ∀ v, 0 ≤ e v) (ρ : F) :
    sphereCount (gramF (classForm Q₀ c)) (fun _ => 1) ρ 𝔟 =
      (repCount (formF Q₀) (scaleLat e he c.out) (β ^ 2 * ρ) : ℝ≥0∞) := by
  have h1 := HilbertModular.sameGenus_out hc
  have h2 := HilbertModular.isIntegral_stdLat Q₀
  have hint : Lattices.IsIntegral (formF Q₀) c.out.1 := Lattices.SameGenus.isIntegral (formF Q₀) h2 h1
  have hint' : Lattices.IsIntegral (formF Q₀) (scaleLat e he c.out).1 := isIntegral_scaleLat _ hpos hint
  have hfinR : Finite {w : Fin N → F // w ∈ (scaleLat e he c.out).1 ∧ (formF Q₀).eval w = β ^ 2 * ρ} :=
    finite_repSet hpd (scaleLat e he c.out).2 hint' (β ^ 2 * ρ)
  classical
  obtain ⟨γ, hi, hout, hcf⟩ := classForm_spec' Q₀ hfree hc
  have hcout : c.out = ⟨Lattices.latOf γ, hout ▸ c.out.2⟩ := Subtype.ext hout
  set P : (Fin N → F) → Prop := fun η => qv (gramF (classForm Q₀ c)) η = ρ ∧ LatMem (twist 𝔟 fun _ => 1) η
  have hP : ∀ η, P η ↔ (∀ i, η i ∈ ((𝔟 : FractionalIdeal (𝓞 F)⁰ F))⁻¹) ∧ (formF Q₀).eval (γ.val *ᵥ η) = ρ := by
    intro η
    simp only [P, hcf, qv_gramF, gramZ_map, eval_gramFormF_col, LatMem, twist]
    rw [and_comm]
    refine and_congr ?_ Iff.rfl
    refine forall_congr' fun i => ?_
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_one, mul_one]
    rfl
  have hmem : ∀ η, γ.val *ᵥ (β • η) ∈ (scaleLat e he c.out).1 ↔ ∀ i, η i ∈ ((𝔟 : FractionalIdeal (𝓞 F)⁰ F))⁻¹ := by
    intro η
    rw [hcout]
    exact mem_scaleLat_latOf_iff γ _ 𝔟 hβ e he hev η
  have hto : ∀ η : {η // P η}, γ.val *ᵥ (β • η.1) ∈ (scaleLat e he c.out).1 ∧
      (formF Q₀).eval (γ.val *ᵥ (β • η.1)) = β ^ 2 * ρ := by
    intro η
    obtain ⟨h1, h2⟩ := (hP η.1).mp η.2
    refine ⟨(hmem η.1).mpr h1, ?_⟩
    rw [mulVec_smul, eval_smul_gen, h2]
  have hγβ : ∀ w : Fin N → F, γ.val *ᵥ (β • (β⁻¹ • (γ⁻¹.val *ᵥ w))) = w := fun w => by
    rw [smul_smul, mul_inv_cancel₀ hβ, one_smul, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, one_mulVec]
  have hinv : ∀ w : {w : Fin N → F // w ∈ (scaleLat e he c.out).1 ∧ (formF Q₀).eval w = β ^ 2 * ρ},
      P (β⁻¹ • (γ⁻¹.val *ᵥ w.1)) := by
    intro w
    rw [hP]
    obtain ⟨hw, hQ⟩ := w.2
    refine ⟨(hmem _).mp (by rw [hγβ]; exact hw), ?_⟩
    rw [mulVec_smul, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec,
      eval_smul_gen, hQ, inv_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hβ), one_mul]
  let eqv : {η // P η} ≃ {w : Fin N → F // w ∈ (scaleLat e he c.out).1 ∧ (formF Q₀).eval w = β ^ 2 * ρ} :=
    { toFun := fun η => ⟨γ.val *ᵥ (β • η.1), hto η⟩
      invFun := fun w => ⟨β⁻¹ • (γ⁻¹.val *ᵥ w.1), hinv w⟩
      left_inv := fun η => Subtype.ext (show β⁻¹ • (γ⁻¹.val *ᵥ (γ.val *ᵥ (β • η.1))) = η.1 by
        rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec, smul_smul,
          inv_mul_cancel₀ hβ, one_smul])
      right_inv := fun w => Subtype.ext (hγβ w.1) }
  have hfinP : Finite {η // P η} := Finite.of_equiv _ eqv.symm
  have hfinS : {η | P η}.Finite := Set.finite_coe_iff.mp hfinP
  unfold sphereCount
  rw [tsum_eq_sum (s := hfinS.toFinset) (fun η hη => by
    rw [Set.Finite.mem_toFinset] at hη; exact if_neg hη)]
  rw [Finset.sum_boole, Finset.filter_true_of_mem]
  · rw [repCount, ← Nat.card_congr eqv, show Nat.card {η // P η} = Nat.card ↥{η | P η} from rfl,
      Nat.card_eq_card_finite_toFinset hfinS]
  · intro η hη
    exact ((Set.Finite.mem_toFinset hfinS).mp hη : P η)

end Bridge

/-! ### The per-ideal identity for every fractional ideal -/

section PerIdealNF

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

open FractionalIdeal

/-- The frame's local type sum at any $t$ with $|t| = |\varpi^j|$ is $W_\mathfrak p(j)$ (`locTypeSumG_unit`). -/
theorem locTypeSumG_frame_eq_locW_of_valued (v : HeightOneSpectrum (𝓞 F)) {Q : QuadForm F (n + 1)} {ρ : F}
    (fr : AdaptedFrame Q ρ) (hQ' : fr.Q'.Nondegenerate) {t : v.adicCompletion F} {j : ℤ}
    (ht : Valued.v t = WithZero.exp (-j)) :
    locTypeSumG v ρ (fr.Q'.map (algebraMap (𝓞 F) F)) (frameLat v fr.g) t = locW v fr j := by
  have hQF' : (fr.Q'.map (algebraMap (𝓞 F) F)).Nondegenerate := by
    rw [QuadForm.Nondegenerate, hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hQ'
  have hval : Valued.v (t * unifV v ^ (-j)) = 1 := by
    rw [map_mul, ht, valued_unifV_zpow, ← WithZero.exp_add, show -j + -(-j) = 0 by ring, WithZero.exp_zero]
  set u : v.adicCompletionIntegers F := toO v _ hval.le
  have hu : IsUnit u := by
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]; exact hval
  have htu : t = (u : v.adicCompletion F) * unifV v ^ j := by
    show t = (t * unifV v ^ (-j)) * unifV v ^ j
    rw [mul_assoc, ← zpow_add₀ (unifV_ne_zero v), neg_add_cancel, zpow_zero, mul_one]
  have hΛ : (frameLat v fr.g).IsLattice (v.adicCompletion F) := loc_isLattice v (glImage_isLattice _ intVec_isLattice)
  rw [htu, show ((u : v.adicCompletionIntegers F) : v.adicCompletion F) = ((hu.unit : (v.adicCompletionIntegers F)ˣ) :
      v.adicCompletionIntegers F) from rfl, locTypeSumG_unit v ρ _ hQF' hΛ (unifV v ^ j) hu.unit]
  rfl

theorem exists_mem_ne_zero_fracIdeal (𝔟 : FracIdeal F) : ∃ β ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F), β ≠ 0 := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  apply 𝔟.ne_zero
  ext x
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · rw [h x hx]; exact zero_mem _
  · rw [FractionalIdeal.mem_zero_iff] at hx; rw [hx]; exact zero_mem _

open QuadFormsKB.SphericalFibration in
/-- **The per-ideal identity for every fractional ideal $\mathfrak b$** (any class number; Weil 1982, §4.5, p. 109 [unverified]):
$$\sum_{\mathrm{cls}M\subseteq\mathrm{gen}\,\mathcal O_F^{n+1}}\frac{\#\{\eta\in\mathfrak b^{-1}M : Q(\eta) = \rho\}}{|O(M)|} =
\mathrm{Mass}(Q_0')\prod_\mathfrak pW_\mathfrak p(\mathrm{ord}_\mathfrak p\mathfrak b).$$ -/
@[kb "weil1982" "§4.5, p. 109 (the term of the ideal b in the orbital Euler product) [unverified]"]
theorem finsum_sphereCount_eq_nf (Q₀ : QuadForm (𝓞 F) (n + 1)) (hpd : IsTotallyPosDef (formF Q₀)) {ρ : F}
    (hρ : ρ ≠ 0) (fr : AdaptedFrame (formF Q₀) ρ) (𝔟 : FracIdeal F) :
    ∑ᶠ c ∈ genusClasses (formF Q₀) (stdLat F (n + 1)),
        sphereCount (gramF (classForm Q₀ c)) (fun _ => 1) ρ 𝔟 *
          ENNReal.ofReal ((LatClass.autCard (formF Q₀) c : ℝ))⁻¹ =
      ENNReal.ofReal (mass (fr.Q'.map (algebraMap (𝓞 F) F)) (stdLat F n) *
        ∏ᶠ v, locW v fr (count F v (𝔟 : FractionalIdeal (𝓞 F)⁰ F))) := by
  classical
  set I : FractionalIdeal (𝓞 F)⁰ F := (𝔟 : FractionalIdeal (𝓞 F)⁰ F)
  have hI : I ≠ 0 := 𝔟.ne_zero
  obtain ⟨β, hβI, hβ⟩ := exists_mem_ne_zero_fracIdeal 𝔟
  set e : HeightOneSpectrum (𝓞 F) → ℤ := fun v => count F v (spanSingleton (𝓞 F)⁰ β) - count F v I
  have he : ∀ᶠ v in Filter.cofinite, e v = 0 :=
    ((finite_factors (spanSingleton (𝓞 F)⁰ β)).and (finite_factors I)).mono fun v h => by
      simp only [e, h.1, h.2, sub_zero]
  have hpos : ∀ v, 0 ≤ e v := by
    intro v
    have h1 := (Analysis.mem_iff_forall_valuation_le hI β).mp hβI v
    rw [Analysis.valuation_eq_exp_neg_count v hβ, WithZero.exp_le_exp] at h1
    simp only [e]; omega
  have hfree := genusFree_formF hpd
  have hQF : (formF Q₀).Nondegenerate := hpd.nondegenerate
  have hQ'nd : fr.Q'.Nondegenerate := fr.nondegenerate hQF hρ
  have hLi : Lattices.IsIntegral (formF Q₀) (scaleLat e he (stdLat F (n + 1))).1 :=
    isIntegral_scaleLat _ hpos (HilbertModular.isIntegral_stdLat Q₀)
  -- the class sum is the genus sum of the non-free lattice `ϖ^e 𝓞_F^{n+1}`
  have hfin := genusClasses_finite hpd (stdLat F (n + 1)) (HilbertModular.isIntegral_stdLat Q₀)
  have hL : ∑ᶠ c ∈ genusClasses (formF Q₀) (stdLat F (n + 1)),
      sphereCount (gramF (classForm Q₀ c)) (fun _ => 1) ρ 𝔟 *
        ENNReal.ofReal ((LatClass.autCard (formF Q₀) c : ℝ))⁻¹ =
      ENNReal.ofReal (repMass (formF Q₀) (scaleLat e he (stdLat F (n + 1))) (β ^ 2 * ρ)) := by
    rw [repMass_scaleLat, finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
      ENNReal.ofReal_sum_of_nonneg (fun c _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hcg := hfin.mem_toFinset.mp hc
    rw [sphereCount_eq_repCount_scale Q₀ hpd hfree hcg 𝔟 hβ e he (fun v => rfl) hpos, div_eq_mul_inv,
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  rw [hL, repMass_eq_mass_mul_finprod_lat Q₀ hpd hρ fr hβ _ hLi]
  congr 2
  refine finprod_congr fun v => ?_
  -- the local factor
  have hloc : loc v (glImage fr.g⁻¹ (scaleLat e he (stdLat F (n + 1))).1) =
      locAct v (scalGL v (e v)) (frameLat v fr.g) := by
    rw [loc_glImage, loc_scaleLat, ← locAct_mul, ← scalGL_comm, locAct_mul, frameLat, loc_glImage]
  have hΛ : (frameLat v fr.g).IsLattice (v.adicCompletion F) := loc_isLattice v (glImage_isLattice _ intVec_isLattice)
  have hQF' : (fr.Q'.map (algebraMap (𝓞 F) F)).Nondegenerate := by
    rw [QuadForm.Nondegenerate, hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hQ'nd
  have hβe : algebraMap F (v.adicCompletion F) β =
      unifV v ^ e v * (unifV v ^ (-e v) * algebraMap F (v.adicCompletion F) β) := by
    rw [← mul_assoc, ← zpow_add₀ (unifV_ne_zero v), add_neg_cancel, zpow_zero, one_mul]
  rw [hloc, hβe, locTypeSumG_scale v ρ _ hQF' (e v) hΛ]
  refine locTypeSumG_frame_eq_locW_of_valued v fr hQ'nd ?_
  rw [map_mul, valued_unifV_zpow, valued_algebraMap, Analysis.valuation_eq_exp_neg_count v hβ, ← WithZero.exp_add]
  congr 1
  simp only [e]; ring

end PerIdealNF

/-! ### The orbital Euler product, $\tau = 2$ and the mass formula over every totally real field -/

section EulerNF

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

open QuadFormsKB.SphericalFibration QuadFormsKB.SphericalZeta FractionalIdeal in
/-- **Steps 1–5: the orbital series is an Euler product** (Weil 1982, §4.5, p. 109 [unverified]). For **every** totally real $F$ (any class number), $Q_0$ totally
positive definite in $n + 1 \ge 5$ variables, $\rho = \rho_k$, an adapted frame and the local orbital identity at every prime,
$$D_k(s) = \mathrm{Mass}(Q_0')\cdot\frac{\prod_\mathfrak p\alpha_\mathfrak p(Q_0')\prod_\mathfrak pD_\mathfrak p\prod_\mathfrak pZ_\mathfrak p(s,\rho)}{\prod_\mathfrak p\alpha_\mathfrak p(Q_0)}\qquad(s > 0),$$
$D_k$ = `orbitalSeries`, $D_\mathfrak p$ = `frameD`, $Z_\mathfrak p$ = `sphLocal`. -/
theorem orbitalSeries_toReal_eq_nf (Q₀ : QuadForm (𝓞 F) (n + 1))
    (hpd : IsTotallyPosDef (formF Q₀)) (hn : 4 ≤ n) (k : SqClasses F) (fr : AdaptedFrame (formF Q₀) (rep k))
    (hgli : ∀ v, OrbitalLocalIdentityAt v Q₀ fr) {s : ℝ} (hs : 0 < s) :
    (orbitalSeries Q₀ s k).toReal = mass (fr.Q'.map (algebraMap (𝓞 F) F)) (stdLat F n) *
      ((∏' v, NF.siegelDensity v fr.Q' fr.Q') * (∏' v, frameD fr s v) *
        (∏' v, sphLocal Q₀ v (algebraMap F (v.adicCompletion F) (rep k)) s) / ∏' v, NF.siegelDensity v Q₀ Q₀) := by
  classical
  have hρ : rep k ≠ 0 := rep_ne_zero k
  have hQF : (formF Q₀).Nondegenerate := hpd.nondegenerate
  have hQ₀ : Q₀.Nondegenerate := by
    have := hQF
    rw [QuadForm.Nondegenerate, hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
    exact fun h => this (by rw [h, map_zero])
  have hQ'nd : fr.Q'.Nondegenerate := fr.nondegenerate hQF hρ
  set QF' := fr.Q'.map (algebraMap (𝓞 F) F)
  set x : ℝ := ((n + 1 : ℕ) : ℝ) + 2 * s
  set f : HeightOneSpectrum (𝓞 F) → ℤ → ℝ := fun v j =>
    ((Ideal.absNorm v.asIdeal : ℝ) ^ j) ^ (-x) * locW v fr j
  set α : HeightOneSpectrum (𝓞 F) → ℝ := fun v => NF.siegelDensity v Q₀ Q₀
  set α' : HeightOneSpectrum (𝓞 F) → ℝ := fun v => NF.siegelDensity v fr.Q' fr.Q'
  set Z : HeightOneSpectrum (𝓞 F) → ℝ := fun v => sphLocal Q₀ v (algebraMap F (v.adicCompletion F) (rep k)) s
  set D : HeightOneSpectrum (𝓞 F) → ℝ := frameD fr s
  have hqpos : ∀ v : HeightOneSpectrum (𝓞 F), (0 : ℝ) < Ideal.absNorm v.asIdeal := fun v => by
    exact_mod_cast Nat.pos_of_ne_zero ((Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors).mpr
      (mem_nonZeroDivisors_of_ne_zero v.ne_bot))
  -- the local series
  have hloc : ∀ v, HasSum (f v) (α' v * D v * Z v / α v) := by
    intro v
    have h := hasSum_locW v Q₀ hQ₀ hρ fr (hgli v) hs.le
    convert h using 1
    simp only [α', D, Z, α, frameD]
    have hα := siegelDensity_pos v Q₀ hQ₀
    field_simp
  have hf0 : ∀ v j, 0 ≤ f v j := fun v j =>
    mul_nonneg (Real.rpow_nonneg (zpow_nonneg (hqpos v).le _) _) (locTypeSumG_nonneg v)
  -- the exceptional set
  have hfin₀ : {v : HeightOneSpectrum (𝓞 F) | frameLat v fr.g ≠ std v ∨ v.valuation F (rep k) ≠ 1 ∨
      v.valuation F 2 ≠ 1}.Finite := by
    refine ((Filter.eventually_cofinite.mp (loc_eventually_std (glImage_isLattice fr.g⁻¹ intVec_isLattice))).union
      ((finite_valuation_ne_one hρ).union (finite_valuation_ne_one (two_ne_zero (α := F))))).subset fun v hv => ?_
    simpa [frameLat, or_assoc] using hv
  set S₀ := hfin₀.toFinset
  have hW0 : ∀ v ∉ S₀, locW v fr 0 = 1 := by
    intro v hv
    simp only [S₀, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or, not_not] at hv
    unfold locW
    rw [zpow_zero, hv.1]
    exact locTypeSumG_std_one_of_units v fr.Q' hQ'nd hv.2.1 hv.2.2
  have hf1 : ∀ v ∉ S₀, f v 0 = 1 := by
    intro v hv
    simp only [f, zpow_zero, Real.one_rpow, one_mul]
    exact hW0 v hv
  -- the Euler product
  have hαm : Multipliable α := multipliable_siegelDensity (N := n + 1) (by omega) (by omega) Q₀ hQ₀
  have hα'm : Multipliable α' := multipliable_siegelDensity (N := n) (by omega) (by omega) fr.Q' hQ'nd
  have hZm : Multipliable Z := multipliable_zf (Q := Q₀) hQ₀ (by omega) (Quotient.out k) hs.le
  have hDm : Multipliable D := by
    have hfinD := finite_frameD_ne_one fr hρ s
    refine multipliable_of_ne_finset_one (s := hfinD.toFinset) fun v hv => ?_
    by_contra h
    exact hv ((Set.Finite.mem_toFinset _).mpr h)
  have hαpos := tprod_siegelDensity_pos (N := n + 1) (by omega) Q₀ hQ₀
  have hP : HasProd (fun v => ∑' j, f v j) ((∏' v, α' v) * (∏' v, D v) * (∏' v, Z v) / ∏' v, α v) := by
    have e : (fun v => ∑' j, f v j) = fun v => α' v * D v * Z v / α v := funext fun v => (hloc v).tsum_eq
    rw [e]
    exact ((hα'm.hasProd.mul hDm.hasProd).mul hZm.hasProd).div₀ hαm.hasProd hαpos.ne'
  have hE := hasSum_finsupp_finprod f hf0 S₀ hf1 (fun v => (hloc v).summable) hP
  have hEb : HasSum (fun 𝔟 : FracIdeal F => ∏ᶠ v, f v (count F v (𝔟 : FractionalIdeal (𝓞 F)⁰ F)))
      ((∏' v, α' v) * (∏' v, D v) * (∏' v, Z v) / ∏' v, α v) := by
    have := (fracIdealEquiv F).hasSum_iff.mpr hE
    convert this using 2 with 𝔟
    simp only [Function.comp_apply, fracIdealEquiv_apply]
  have hpd' : IsTotallyPosDef QF' := by
    have h1 := isTotallyPosDef_compMat (formF Q₀) fr.g hpd
    rw [fr.compMat_eq] at h1
    exact isTotallyPosDef_of_splitForm h1
  have hmass : 0 < mass QF' (stdLat F n) := mass_pos hpd' (stdLat F n) (HilbertModular.isIntegral_stdLat fr.Q')
  have hterm : ∀ 𝔟 : FracIdeal F,
      ENNReal.ofReal (idealNorm F 𝔟 ^ (-(((n + 1 : ℕ) : ℝ) + 2 * s))) *
        ∑ᶠ c ∈ genusClasses (formF Q₀) (stdLat F (n + 1)),
          sphereCount (gramF (classForm Q₀ c)) (fun _ => 1) (rep k) 𝔟 *
            ENNReal.ofReal ((LatClass.autCard (formF Q₀) c : ℝ))⁻¹ =
      ENNReal.ofReal (mass QF' (stdLat F n) * ∏ᶠ v, f v (count F v (𝔟 : FractionalIdeal (𝓞 F)⁰ F))) := by
    intro 𝔟
    set I : FractionalIdeal (𝓞 F)⁰ F := (𝔟 : FractionalIdeal (𝓞 F)⁰ F)
    rw [finsum_sphereCount_eq_nf Q₀ hpd hρ fr 𝔟]
    -- everything is a product over a finite set `T`
    have hcfin : {v : HeightOneSpectrum (𝓞 F) | count F v I ≠ 0}.Finite :=
      Filter.eventually_cofinite.mp (finite_factors I)
    set T := hcfin.toFinset ∪ S₀
    have hcT : ∀ v ∉ T, count F v I = 0 := by
      intro v hv; by_contra h; exact hv (Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).mpr h))
    have hS₀T : ∀ v ∉ T, v ∉ S₀ := fun v hv h => hv (Finset.mem_union_right _ h)
    have e1 : idealNorm F 𝔟 = ∏ v ∈ T, (Ideal.absNorm v.asIdeal : ℝ) ^ count F v I := by
      rw [idealNorm_eq_finprod]
      refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
      by_contra h; apply hv
      show (Ideal.absNorm v.asIdeal : ℝ) ^ count F v I = 1
      rw [hcT v h, zpow_zero]
    have e2 : ∏ᶠ v, locW v fr (count F v I) = ∏ v ∈ T, locW v fr (count F v I) := by
      refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
      by_contra h; apply hv
      show locW v fr (count F v I) = 1
      rw [hcT v h]; exact hW0 v (hS₀T v h)
    have e3 : ∏ᶠ v, f v (count F v I) = ∏ v ∈ T, f v (count F v I) := by
      refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
      by_contra h; apply hv
      show f v (count F v I) = 1
      rw [hcT v h]; exact hf1 v (hS₀T v h)
    rw [e1, e2, e3, ← Real.finsetProd_rpow _ _ (fun v _ => zpow_nonneg (hqpos v).le _),
      ← ENNReal.ofReal_mul (Finset.prod_nonneg fun v _ => Real.rpow_nonneg (zpow_nonneg (hqpos v).le _) _)]
    congr 1
    simp only [f, Finset.prod_mul_distrib]
    ring
  show (∑' 𝔟 : FracIdeal F, ENNReal.ofReal (idealNorm F 𝔟 ^ (-(((n + 1 : ℕ) : ℝ) + 2 * s))) *
        ∑ᶠ c ∈ genusClasses (formF Q₀) (stdLat F (n + 1)),
          sphereCount (gramF (classForm Q₀ c)) (fun _ => 1) (rep k) 𝔟 *
            ENNReal.ofReal ((LatClass.autCard (formF Q₀) c : ℝ))⁻¹).toReal = _
  simp_rw [hterm]
  have hnn : ∀ 𝔟 : FracIdeal F, 0 ≤ mass QF' (stdLat F n) * ∏ᶠ v, f v (count F v (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) :=
    fun 𝔟 => mul_nonneg hmass.le (finprod_nonneg fun v => hf0 v _)
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn (hEb.summable.mul_left _), ENNReal.toReal_ofReal (tsum_nonneg hnn),
    tsum_mul_left, hEb.tsum_eq]

open QuadFormsKB.SphericalFibration QuadFormsKB.SphericalZeta Classical in
/-- **The orbital Euler product for one square class** (Weil 1982, §4.5, p. 109; any class number): for $Q_0$ totally positive definite
in $N = n + 1 \ge 5$ variables, $\rho = \rho_k$ totally positive, an adapted frame $Q_0\circ g = \langle\rho\rangle\perp Q_0'$ and the local orbital
identity of the frame at every prime,
$$2\mu\,D_k(s) = \tau(SO(Q_0'))\,|d_F|^{-\frac{N-1}2}\prod_w\frac{2\pi^{N/2}\sigma_w(\rho)^{\frac N2+s}}{\Gamma(\frac N2)\sqrt{\det A_w}}\prod_\mathfrak pZ_\mathfrak p(s,\rho).$$
The constant is the stabilizer's $\tau(SO(Q_0')) = 2\mu(Q_0')\mathrm{Mass}(Q_0')$ (`tauSO`); no induction hypothesis is used here. -/
@[kb "weil1982" "§4.5, p. 109 (Z⁺(s) unfolded over T(ρ), the orbital Euler product) [unverified]"]
theorem two_mul_tamagawaK_orbitalSeries_nf (Q₀ : QuadForm (𝓞 F) (n + 1))
    (hpd : IsTotallyPosDef (formF Q₀)) (hn : 4 ≤ n) (k : SqClasses F) (fr : AdaptedFrame (formF Q₀) (rep k))
    (hgli : ∀ v, OrbitalLocalIdentityAt v Q₀ fr) {s : ℝ} (hs : 0 < s)
    (hpos : ∀ v : InfinitePlace F, 0 < realEmb F v (rep k)) :
    2 * tamagawaK Q₀ * (orbitalSeries Q₀ s k).toReal =
      tauSO fr.Q' * |(NumberField.discr F : ℝ)| ^ (-(((n + 1 : ℕ) : ℝ) - 1) / 2) *
        (∏ w, orbitalArch Q₀ s (rep k) w) *
        ∏' v : HeightOneSpectrum (𝓞 F), sphLocal Q₀ v (algebraMap F (v.adicCompletion F) (rep k)) s := by
  have hρ : rep k ≠ 0 := rep_ne_zero k
  have hQF : (formF Q₀).Nondegenerate := hpd.nondegenerate
  have hQ₀ : Q₀.Nondegenerate := by
    have := hQF
    rw [QuadForm.Nondegenerate, hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
    exact fun h => this (by rw [h, map_zero])
  have hQ'nd : fr.Q'.Nondegenerate := fr.nondegenerate hQF hρ
  have hpd' : IsTotallyPosDef (fr.Q'.map (algebraMap (𝓞 F) F)) := by
    have h1 := isTotallyPosDef_compMat (formF Q₀) fr.g hpd
    rw [fr.compMat_eq] at h1
    exact isTotallyPosDef_of_splitForm h1
  rw [orbitalSeries_toReal_eq_nf Q₀ hpd hn k fr hgli hs]
  have htau : tauSO fr.Q' = tamagawaK fr.Q' * (2 * mass (fr.Q'.map (algebraMap (𝓞 F) F)) (stdLat F n)) := by
    rw [tauSO, mass_SO_eq_two_mul_mass fr.Q' hQ'nd (by omega) hpd' (HilbertModular.isIntegral_stdLat fr.Q')]
  rw [htau]
  -- the frame factors through the product formula
  have hDfin : Function.HasFiniteMulSupport (frameD fr s) := by
    have := finite_frameD_ne_one fr hρ s
    exact this.subset fun v hv => hv
  rw [tprod_eq_finprod hDfin, finprod_frameD fr hρ s]
  set A := ∏' v : HeightOneSpectrum (𝓞 F), NF.siegelDensity v Q₀ Q₀
  set A' := ∏' v : HeightOneSpectrum (𝓞 F), NF.siegelDensity v fr.Q' fr.Q'
  set Z := ∏' v : HeightOneSpectrum (𝓞 F), sphLocal Q₀ v (algebraMap F (v.adicCompletion F) (rep k)) s
  set M := mass (fr.Q'.map (algebraMap (𝓞 F) F)) (stdLat F n)
  set δ := |(NumberField.discr F : ℝ)|
  have hδ : 0 < δ := abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero F)
  have hA : A ≠ 0 := (tprod_siegelDensity_pos (N := n + 1) (by omega) Q₀ hQ₀).ne'
  -- the archimedean products
  have key : (∏ σ : F →ₐ[ℚ] ℂ, archVolSO (n + 1) (detGram Q₀ σ)) *
      (∏ σ : F →ₐ[ℚ] ℂ, (‖σ fr.g.val.det‖ ^ (n + 1))⁻¹ * ‖σ (2 * rep k)‖ ^ n * ‖σ (rep k)‖ ^ (1 + s) * ‖σ 2‖) =
      (∏ σ : F →ₐ[ℚ] ℂ, archVolSO n (detGram fr.Q' σ)) * ∏ w, orbitalArch Q₀ s (rep k) w := by
    rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl fun σ _ => arch_place Q₀ hpd fr hpos s σ,
      Finset.prod_mul_distrib]
    congr 1
    exact Fintype.prod_equiv embPlace _ _ fun σ => rfl
  have hδe : δ ^ (-((((n + 1 : ℕ) : ℝ)) * (((n + 1 : ℕ) : ℝ) - 1) / 4)) =
      δ ^ (-((n : ℝ) * ((n : ℝ) - 1) / 4)) * δ ^ (-(((n + 1 : ℕ) : ℝ) - 1) / 2) := by
    rw [← Real.rpow_add hδ]; push_cast; ring_nf
  unfold tamagawaK
  rw [hδe]
  calc 2 * (δ ^ (-((n : ℝ) * ((n : ℝ) - 1) / 4)) * δ ^ (-(((n + 1 : ℕ) : ℝ) - 1) / 2) *
        (∏ σ : F →ₐ[ℚ] ℂ, archVolSO (n + 1) (detGram Q₀ σ)) * A) *
        (M * (A' * (∏ σ : F →ₐ[ℚ] ℂ, (‖σ fr.g.val.det‖ ^ (n + 1))⁻¹ * ‖σ (2 * rep k)‖ ^ n *
          ‖σ (rep k)‖ ^ (1 + s) * ‖σ 2‖) * Z / A))
      = 2 * (δ ^ (-((n : ℝ) * ((n : ℝ) - 1) / 4)) * δ ^ (-(((n + 1 : ℕ) : ℝ) - 1) / 2)) * M * A' * Z *
          ((∏ σ : F →ₐ[ℚ] ℂ, archVolSO (n + 1) (detGram Q₀ σ)) *
            (∏ σ : F →ₐ[ℚ] ℂ, (‖σ fr.g.val.det‖ ^ (n + 1))⁻¹ * ‖σ (2 * rep k)‖ ^ n *
              ‖σ (rep k)‖ ^ (1 + s) * ‖σ 2‖)) := by
        field_simp
    _ = _ := by rw [key]; ring

open QuadFormsKB.SphericalFibration QuadFormsKB.SphericalZeta Classical in
/-- **The orbital Euler product holds** (`OrbitalEulerProduct`, Weil 1982, §4.5, p. 109), for **every** totally real $F$ (any class number), $Q_0$ totally positive
definite in $n + 1 \ge 5$ variables, with $\tau'_k = \tau(SO(Q_{0,k}'))$ the Tamagawa numbers of the complements (`tauComp`), given the local
orbital identities at the finitely many non-standard primes of each frame (`OrbitalLocalIdentities`). -/
@[kb "weil1982" "§4.5, p. 109 (the orbital Euler product: Siegel's theorem for the numbers ρb² with τ(G'), summed over 𝔟)"]
theorem orbitalEulerProduct_nf (Q₀ : QuadForm (𝓞 F) (n + 1))
    (hpd : IsTotallyPosDef (formF Q₀)) (hn : 4 ≤ n) (hloc : OrbitalLocalIdentities Q₀) :
    OrbitalEulerProduct Q₀ (tauComp Q₀) := by
  have hQF : (formF Q₀).Nondegenerate := hpd.nondegenerate
  have hQ₀ : Q₀.Nondegenerate := by
    have := hQF
    rw [QuadForm.Nondegenerate, hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
    exact fun h => this (by rw [h, map_zero])
  refine ⟨fun k s hs hpos => ?_⟩
  by_cases h : ∃ ξ, (formF Q₀).eval ξ = rep k
  · rw [tauComp, dif_pos h]
    exact two_mul_tamagawaK_orbitalSeries_nf Q₀ hpd hn k (chosenFrame Q₀ k h)
      (fun v => orbitalLocalIdentityAt_all hloc hQ₀ (by omega) (rep_ne_zero k) _ v) hs hpos
  · rw [orbitalSeries_eq_zero_of_not_rep Q₀ (genusFree_formF hpd) k h s,
      tprod_sphLocal_eq_zero Q₀ hpd (rep_ne_zero k) hpos h s]
    simp

/-- **Weil's Theorem 4.5.1, $\tau(SO(V)) = 2$, from the induction hypothesis** (Weil 1982, §4.5, Thm 4.5.1, p. 109): for $F$ totally real
(**any class number**) and $Q_0$ totally positive definite in $n + 1 \ge 5$ variables over $\mathcal O_F$, if $\tau(SO) = 2$ in rank $n$
(`hIH`, the induction hypothesis: every totally positive definite form in $n$ variables) and the local orbital identities hold at the
non-standard primes of the frames (`OrbitalLocalIdentities`, a per-prime local input), then $\tau(SO(V)) = 2$. -/
@[kb "weil1982" "§4.5, Thm 4.5.1, p. 109 (induction step n → n+1)"]
theorem tamagawaNumberTwo_of_complement_nf (Q₀ : QuadForm (𝓞 F) (n + 1))
    (hpd : IsTotallyPosDef (formF Q₀)) (hn : 4 ≤ n) (hloc : OrbitalLocalIdentities Q₀)
    (hIH : ∀ Q' : QuadForm (𝓞 F) n, IsTotallyPosDef (formF Q') → TamagawaNumberTwo Q') :
    TamagawaNumberTwo Q₀ := by
  have hQF : (formF Q₀).Nondegenerate := hpd.nondegenerate
  have hQ₀ : Q₀.Nondegenerate := by
    have := hQF
    rw [QuadForm.Nondegenerate, hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
    exact fun h => this (by rw [h, map_zero])
  exact SphericalFibration.tamagawaNumberTwo_of_orbitalEulerProduct' Q₀ hQ₀ (by omega) hpd
    (orbitalEulerProduct_nf Q₀ hpd hn hloc) (complementTauTwo_of_IH Q₀ hpd hIH)

/-- **The mass formula in rank $n + 1 \ge 5$ from the induction hypothesis** (`massFormula` with the $\tau = 2$):
$\mathrm{Mass}(\mathcal O_F^{n+1}) = \mu_{\mathrm{Tam}}(K_{SO})^{-1}$. -/
@[kb "weil1982" "§4.5, Thm 4.5.1, p. 109; cf. Kitaoka 1993, Thm 6.8.1 [unverified]"]
theorem massFormula_of_complement_nf (Q₀ : QuadForm (𝓞 F) (n + 1))
    (hpd : IsTotallyPosDef (formF Q₀)) (hn : 4 ≤ n) (hloc : OrbitalLocalIdentities Q₀)
    (hIH : ∀ Q' : QuadForm (𝓞 F) n, IsTotallyPosDef (formF Q') → TamagawaNumberTwo Q') :
    mass (formF Q₀) (stdLat F (n + 1)) = (tamagawaK Q₀)⁻¹ := by
  have hQF : (formF Q₀).Nondegenerate := hpd.nondegenerate
  have hQ₀ : Q₀.Nondegenerate := by
    have := hQF
    rw [QuadForm.Nondegenerate, hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
    exact fun h => this (by rw [h, map_zero])
  exact massFormula Q₀ hQ₀ (by omega) hpd (HilbertModular.isIntegral_stdLat Q₀)
    (tamagawaNumberTwo_of_complement_nf Q₀ hpd hn hloc hIH)

/-- **Siegel's formula for the number $m$ in rank $n + 1 \ge 5$** for split forms $\langle m\rangle\perp Q_0'$ (`siegelFormulaAt_of_tamagawa'` with the $\tau = 2$ in rank $n + 1$; $\tau(SO(Q_0')) = 2$ is part of the induction hypothesis). -/
@[kb "weil1982" "§4.5, p. 100 (Siegel's theorem as a consequence of τ = 2), Thm 4.5.1, p. 109"]
theorem siegelFormulaAt_of_complement_nf (m₀ : 𝓞 F) (hm : m₀ ≠ 0) (Q₀' : QuadForm (𝓞 F) n)
    (hn : 4 ≤ n) (hpd : IsTotallyPosDef (formF (splitForm m₀ Q₀')))
    (hloc : OrbitalLocalIdentities (splitForm m₀ Q₀'))
    (hIH : ∀ Q' : QuadForm (𝓞 F) n, IsTotallyPosDef (formF Q') → TamagawaNumberTwo Q') :
    SiegelFormulaAt (splitForm m₀ Q₀') m₀ := by
  have hpd' : IsTotallyPosDef (formF Q₀') := by
    have := isTotallyPosDef_of_splitForm (m := algebraMap (𝓞 F) F m₀) (Q' := Q₀'.map (algebraMap (𝓞 F) F))
      (by rw [← map_splitForm]; exact hpd)
    exact this
  exact siegelFormulaAt_of_tamagawa' m₀ hm Q₀' (by omega) hpd (HilbertModular.isIntegral_stdLat _)
    (tamagawaNumberTwo_of_complement_nf _ hpd hn hloc hIH) (hIH Q₀' hpd')

end EulerNF

/-! ### Headlines over every totally real field: Weil's induction with even ranks via the orbital Euler product -/

section HeadlineNF

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

open QuadFormsKB.SphericalFibration in
/-- **The orbital Euler product with no input, over every totally real field** (any class number, rank $n + 1 \ge 5$). -/
@[kb "weil1982" "§4.5, p. 109 (the orbital Euler product)"]
theorem orbitalEulerProduct_nf' {n : ℕ} (Q₀ : QuadForm (𝓞 F) (n + 1)) (hpd : IsTotallyPosDef (formF Q₀)) (hn : 4 ≤ n) :
    OrbitalEulerProduct Q₀ (tauComp Q₀) :=
  orbitalEulerProduct_nf Q₀ hpd hn (orbitalLocalIdentities Q₀ (nondegenerate_of_totallyPosDef' hpd))

/-- **$\tau(SO) = 2$ in every rank $N \ge 4$ from rank 4, over every totally real field** (any class number). Weil's induction
$n \to n + 1$ by the orbital Euler product in **every** rank $n + 1 \ge 5$, even ranks included (no Hilbert modular forms, no Smith normal form over
$\mathcal O_F$, no `PrincipalPrimeSupply`); the local orbital identities are proved (`orbitalLocalIdentities`). -/
@[kb "weil1982" "§4.5, Thm 4.5.1, p. 109 (induction n → n+1, every rank)"]
theorem tamagawaNumberTwo_of_quaternary_nf (h4 : QuaternaryTamagawaTwo F) {N : ℕ} (hN : 4 ≤ N)
    (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀)) : TamagawaNumberTwo Q₀ := by
  revert Q₀
  induction N, hN using Nat.le_induction with
  | base => exact h4.tau_eq_two
  | succ n hn ih =>
    intro Q₀ hpd
    exact tamagawaNumberTwo_of_complement_nf Q₀ hpd hn
      (orbitalLocalIdentities Q₀ (nondegenerate_of_totallyPosDef' hpd)) ih

/-- **The mass formula in every rank $N \ge 4$ from rank 4, over every totally real field.** -/
@[kb "weil1982" "§4.5, Thm 4.5.1, p. 109; cf. Kitaoka 1993, Thm 6.8.1 [unverified]"]
theorem massFormula_of_quaternary_nf (h4 : QuaternaryTamagawaTwo F) {N : ℕ} (hN : 4 ≤ N)
    (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀)) : MassFormulaHolds Q₀ :=
  massFormula Q₀ (nondegenerate_of_map hpd.nondegenerate) (by omega) hpd (HilbertModular.isIntegral_stdLat Q₀)
    (tamagawaNumberTwo_of_quaternary_nf h4 hN Q₀ hpd)

/-- **Siegel's formula for numbers in every rank $N \ge 5$ from rank 4, over every totally real field** (odd and even $N$). -/
@[kb "weil1982" "§4.5, p. 100 (Siegel's theorem as a consequence of τ = 2), Thm 4.5.1, p. 109"]
theorem siegelFormulaAt_of_quaternary_nf (h4 : QuaternaryTamagawaTwo F) {n : ℕ} (hn : 4 ≤ n)
    (Q₀ : QuadForm (𝓞 F) (n + 1)) (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F}
    (hm : ∀ v, 0 < realEmb F v (algebraMap (𝓞 F) F m)) : SiegelFormulaAt Q₀ m :=
  siegelFormulaAt_of_local Q₀ hpd (by omega) (orbitalLocalIdentities Q₀ (nondegenerate_of_totallyPosDef' hpd))
    (tamagawaNumberTwo_of_quaternary_nf h4 (by omega) Q₀ hpd)
    (fun Q' hQ' => tamagawaNumberTwo_of_quaternary_nf h4 hn Q' hQ') hm

/-- **The mass formula for the non-free genus of $\varpi^e\mathcal O_F^N$** ($= \mathfrak b\mathcal O_F^N$ for $e = \mathrm{ord}\,\mathfrak b$, every totally
real $F$, $N \ge 4$): $\mathrm{Mass}(\mathfrak b\mathcal O_F^N) = \mathrm{Mass}(\mathcal O_F^N) = \mu_{\mathrm{Tam}}(K_{SO})^{-1}$, from rank 4. -/
@[kb "weil1982" "§4.5, Thm 4.5.1, p. 109 (mass of the genus of bL) [unverified]"]
theorem massFormula_scaleLat_nf (h4 : QuaternaryTamagawaTwo F) {N : ℕ} (hN : 4 ≤ N)
    (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀)) (e : HeightOneSpectrum (𝓞 F) → ℤ)
    (he : ∀ᶠ v in Filter.cofinite, e v = 0) :
    mass (formF Q₀) (scaleLat e he (stdLat F N)) = (tamagawaK Q₀)⁻¹ := by
  rw [mass_scaleLat]; exact massFormula_of_quaternary_nf h4 hN Q₀ hpd

end HeadlineNF

end QuadFormsKB.Tamagawa
