import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereConst
import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereLocalComplex

/-!
# The Tamagawa measure of a product set and the product formula at all places

$F$ any number field. `muTam_prodSet` and `prod_cReal_mul_tprod_cFin` are stated for totally real $F$.
Here, with the complex places:

* **`muTam_prodSetNF`**: for measurable $E_w\subseteq SO(Q)(\mathbb R)$ (real $w$), $E_w\subseteq SO(Q)(\mathbb C)$ (complex
  $w$) and $E_f\subseteq SO(Q)(\mathbb A_f)$,
  $\mu_{\mathrm{Tam}}\big(\prod_wE_w\times E_f\big) = c_F(n)\,2^{n(n-1)r_2/2}\prod_{w\ \mathrm{real}}\mu_w(E_w)
  \prod_{w\ \mathrm{complex}}\mu_w(E_w)\cdot\mu_f(E_f)$ ($\mu_w$ the Leray measures; `cxWeil`, Weil's normalization at the
  complex places);
* **`prod_places_mul_tprod`**: the product formula $\prod_{w\ \mathrm{real}}|x|_w\prod_{w\ \mathrm{complex}}|x|_w^2
  \prod_v\|x\|_v = 1$ for $x\in F^\times$;
* **`prod_cReal_cCx_mul_tprod_cFin`**: the local constants of the sphere orbital identities at all places (real
  `cReal`, complex `cCx`, finite `cFin`) multiply to $1$.
-/

open MeasureTheory Set Matrix
open scoped ENNReal RestrictedProduct

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayReal
  QuadFormsKB.Tamagawa.Measure.LerayComplex

variable {F : Type} [Field F] [NumberField F]

/-! ### Product sets in $SO(V)(\mathbb A)$ -/

/-- **The archimedean box** $\prod_{w\ \mathrm{real}}E_w\times\prod_{w\ \mathrm{complex}}E_w$ in $G_\infty$. -/
def archBoxNF {n : ℕ} (Q : QuadForm (𝓞 F) n) (E : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ArchSO (QRe Q w)))
    (EC : ∀ w : {w : InfinitePlace F // w.IsComplex}, Set (ArchSOC (QCx Q w))) : Set (GInfSO Q) :=
  (Set.pi univ E) ×ˢ (Set.pi univ EC)

open Classical in
theorem muArchTamSO_archBoxNF {n : ℕ} (Q : QuadForm (𝓞 F) n) (hQ' : Q.Nondegenerate)
    (E : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ArchSO (QRe Q w)))
    (EC : ∀ w : {w : InfinitePlace F // w.IsComplex}, Set (ArchSOC (QCx Q w))) :
    muArchTamSO Q hQ' (archBoxNF Q E EC) =
      ENNReal.ofReal (cF F n * cxWeil F n) * ((∏ w, lerayMeasure (QRe Q w) (gramDetR_QRe_ne_zero Q hQ' w) (E w)) *
        ∏ w, lerayMeasureC (QCx Q w) (gramDetC_QCx_ne_zero Q hQ' w) (EC w)) := by
  have : ∀ w : {w : InfinitePlace F // w.IsReal},
      SigmaFinite (lerayMeasure (QRe Q w) (gramDetR_QRe_ne_zero Q hQ' w)) := fun w => by
    have := isHaarMeasure_lerayMeasure (gramDetR_QRe_ne_zero Q hQ' w); infer_instance
  have : ∀ w : {w : InfinitePlace F // w.IsComplex},
      SigmaFinite (lerayMeasureC (QCx Q w) (gramDetC_QCx_ne_zero Q hQ' w)) := fun w => by
    have := isHaarMeasure_lerayMeasureC (gramDetC_QCx_ne_zero Q hQ' w); infer_instance
  have hpr : (Measure.pi fun w : {w : InfinitePlace F // w.IsReal} =>
      lerayMeasure (QRe Q w) (gramDetR_QRe_ne_zero Q hQ' w)) (Set.pi univ E) =
      ∏ w, lerayMeasure (QRe Q w) (gramDetR_QRe_ne_zero Q hQ' w) (E w) := Measure.pi_pi _ _
  have hpc : (Measure.pi fun w : {w : InfinitePlace F // w.IsComplex} =>
      lerayMeasureC (QCx Q w) (gramDetC_QCx_ne_zero Q hQ' w)) (Set.pi univ EC) =
      ∏ w, lerayMeasureC (QCx Q w) (gramDetC_QCx_ne_zero Q hQ' w) (EC w) := Measure.pi_pi _ _
  rw [muArchTamSO, Measure.smul_apply, smul_eq_mul, archBoxNF, LerayArch.muArchNF,
    LerayArch.muArchLeray, Measure.prod_prod]
  erw [hpr, hpc]

open Classical in
/-- **The Tamagawa measure of a product set** (every number field):
$\mu_{\mathrm{Tam}}\big(\prod_wE_w\times E_f\big) = c_F(n)\,2^{n(n-1)r_2/2}\prod_w\mu_w(E_w)\cdot\mu_f(E_f)$, the product over
the real and the complex places. -/
theorem muTam_prodSetNF {n : ℕ} (Q : QuadForm (𝓞 F) n) (hQ' : Q.Nondegenerate)
    (E : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ArchSO (QRe Q w)))
    (EC : ∀ w : {w : InfinitePlace F // w.IsComplex}, Set (ArchSOC (QCx Q w))) (Ef : Set (SOAf Q)) :
    muTam Q hQ' (fun _ => 1) {g | (∀ w, g.1.1 w ∈ E w) ∧ (∀ w, g.1.2 w ∈ EC w) ∧ g.2 ∈ Ef} =
      ENNReal.ofReal (cF F n * cxWeil F n) * ((∏ w, lerayMeasure (QRe Q w) (gramDetR_QRe_ne_zero Q hQ' w) (E w)) *
        ∏ w, lerayMeasureC (QCx Q w) (gramDetC_QCx_ne_zero Q hQ' w) (EC w)) *
        Measure.muFin Q (fun _ => 1) Ef := by
  have : {g : SOAdele Q | (∀ w, g.1.1 w ∈ E w) ∧ (∀ w, g.1.2 w ∈ EC w) ∧ g.2 ∈ Ef} = archBoxNF Q E EC ×ˢ Ef := by
    ext g; simp [archBoxNF, Set.mem_pi, and_assoc]
  rw [this, muTam, Measure.prod_prod, muArchTamSO_archBoxNF]

/-! ### The product formula with the complex places -/

open Classical in
/-- **The product formula** for $x\in F^\times$:
$\prod_{w\ \mathrm{real}}|\sigma_wx|\cdot\prod_{w\ \mathrm{complex}}|\sigma_wx|^2\cdot\prod_v\|x\|_v = 1$. -/
theorem prod_places_mul_tprod {x : F} (hx : x ≠ 0) :
    (∏ w : {w : InfinitePlace F // w.IsReal}, |σR w x|) * (∏ w : {w : InfinitePlace F // w.IsComplex}, ‖σC w x‖ ^ 2) *
      ∏' v : HeightOneSpectrum (𝓞 F), ‖σV v x‖ = 1 := by
  have h := prod_infinitePlace_mul_tprod hx
  rw [← sim_prod_places] at h
  convert h using 3
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [mult_isReal w, pow_one, ← norm_embedding_of_isReal w.2, Real.norm_eq_abs]
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [mult_isComplex w, ← norm_embedding_eq w.1]

namespace AdelicSphereSetup

variable {k : ℕ} {Q₀ : QuadForm (𝓞 F) (k + 1)} {ρ : F} (S : AdelicSphereSetup Q₀ ρ) (hρ : ρ ≠ 0)

include hρ in
/-- **The complex constant in closed form**: $c_w = |x_1|_w^{N}|2\rho|_w^{-k}$ with $|z|_w = |z|^2$. -/
theorem cCx_toReal (w : {w : InfinitePlace F // w.IsComplex}) :
    (S.cCx w).toReal = (‖σC w S.x1‖ ^ 2) ^ (k + 1) * ((‖σC w (2 * ρ)‖ ^ 2) ^ k)⁻¹ := by
  have hd : ‖S.dC w‖ ≠ 0 := norm_ne_zero_iff.mpr (S.dC_ne_zero w)
  have hr : ‖σC w ρ‖ ≠ 0 := norm_ne_zero_iff.mpr ((map_ne_zero _).mpr hρ)
  rw [cCx, ENNReal.toReal_ofReal (by positivity)]
  have e1 : (S.PAt (σC w)).val.det = σC w (algebraMap (𝓞 F) F S.C.G.det) := S.det_PAt (σC w)
  have e2 : S.ccC w = S.dC w ^ 2 * σC w ρ := by
    have hq : qF Q₀ S.ξ.1 = ρ := S.ξ.2
    rw [ccC, dC, S.C.m₀_eq, hq, map_mul, map_pow]
  rw [e1, e2]
  simp only [x1, map_div₀, norm_div, map_mul, map_ofNat, norm_mul, norm_pow]
  rw [show ‖σC w (algebraMap (𝓞 F) F S.C.d)‖ = ‖S.dC w‖ from rfl]
  generalize ‖S.dC w‖ = D at hd ⊢
  generalize ‖σC w (algebraMap (𝓞 F) F S.C.G.det)‖ = Gn
  generalize ‖σC w ρ‖ = R at hr ⊢
  have hD : D ^ 2 * D⁻¹ ^ 2 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hd, one_pow]
  have hD' : D ^ (k * 2) * D⁻¹ ^ (k * 2) = 1 := by rw [← mul_pow, mul_inv_cancel₀ hd, one_pow]
  field_simp
  calc _ = Gn ^ 2 * Gn ^ (k * 2) * D ^ (k * 2) * ‖(2 : ℂ)‖ ^ (k * 2) * R ^ (k * 2) * (D ^ 2 * D⁻¹ ^ 2) *
        (D ^ (k * 2) * D⁻¹ ^ (k * 2)) := by rw [hD, hD']; ring
    _ = _ := by ring

open Classical in
include hρ in
/-- **The local constants multiply to $1$ over all places** (every number field; product formula for $x_1$ and
$x_2 = 2\rho$): $\prod_{w\ \mathrm{real}}c_w\prod_{w\ \mathrm{complex}}c_w\prod_vc_v = 1$. -/
theorem prod_cReal_cCx_mul_tprod_cFin :
    (∏ w : {w : InfinitePlace F // w.IsReal}, (S.cReal w).toReal) *
      (∏ w : {w : InfinitePlace F // w.IsComplex}, (S.cCx w).toReal) * ∏' v, (S.cFin v).toReal = 1 := by
  set T : Finset (HeightOneSpectrum (𝓞 F)) :=
    (mulSupport_finite_norm S.x1_ne_zero).toFinset ∪ (mulSupport_finite_norm (x2_ne_zero hρ)).toFinset
  have h1 : ∀ v ∉ T, ‖σV v S.x1‖ = 1 := fun v hv => by
    by_contra h; exact hv (Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).mpr h))
  have h2 : ∀ v ∉ T, ‖σV v (2 * ρ)‖ = 1 := fun v hv => by
    by_contra h; exact hv (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr h))
  have p1 : ∏' v : HeightOneSpectrum (𝓞 F), ‖σV v S.x1‖ = ∏ v ∈ T, ‖σV v S.x1‖ := tprod_eq_prod h1
  have p2 : ∏' v : HeightOneSpectrum (𝓞 F), ‖σV v (2 * ρ)‖ = ∏ v ∈ T, ‖σV v (2 * ρ)‖ := tprod_eq_prod h2
  have p3 : ∏' v, (S.cFin v).toReal = ∏ v ∈ T, (S.cFin v).toReal :=
    tprod_eq_prod fun v hv => by rw [S.cFin_toReal hρ, h1 v hv, h2 v hv]; simp
  have f1 := prod_places_mul_tprod S.x1_ne_zero
  have f2 := prod_places_mul_tprod (x2_ne_zero hρ)
  rw [p1] at f1
  rw [p2] at f2
  rw [p3]
  simp only [Finset.prod_pow] at f1 f2
  simp only [S.cReal_toReal hρ, S.cCx_toReal hρ, S.cFin_toReal hρ, Finset.prod_mul_distrib, Finset.prod_pow,
    Finset.prod_inv_distrib]
  set a1 := ∏ w : {w : InfinitePlace F // w.IsReal}, |σR w S.x1|
  set a2 := ∏ w : {w : InfinitePlace F // w.IsReal}, |σR w (2 * ρ)|
  set b1 := (∏ w : {w : InfinitePlace F // w.IsComplex}, ‖σC w S.x1‖) ^ 2
  set b2 := (∏ w : {w : InfinitePlace F // w.IsComplex}, ‖σC w (2 * ρ)‖) ^ 2
  set c1 := ∏ v ∈ T, ‖σV v S.x1‖
  set c2 := ∏ v ∈ T, ‖σV v (2 * ρ)‖
  calc a1 ^ (k + 1) * (a2 ^ k)⁻¹ * (b1 ^ (k + 1) * (b2 ^ k)⁻¹) * (c1 ^ (k + 1) * (c2 ^ k)⁻¹)
      = (a1 * b1 * c1) ^ (k + 1) * ((a2 * b2 * c2) ^ k)⁻¹ := by
        rw [mul_pow, mul_pow, mul_pow, mul_pow, mul_inv, mul_inv]; ring
    _ = 1 := by rw [f1, f2]; simp

end AdelicSphereSetup

end QuadFormsKB.Tamagawa.Measure.Weil

end
