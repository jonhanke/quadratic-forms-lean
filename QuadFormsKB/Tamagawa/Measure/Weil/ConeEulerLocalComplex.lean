import QuadFormsKB.Tamagawa.Measure.Weil.ConeEulerBox
import QuadFormsKB.Tamagawa.Measure.ConeComplexOrbit

/-!
# Local facts at a complex place for the cone form
The complex-place analogue of the real-place developments `ConeEulerBase` (`Real` section), `ConeEulerLocalReal` and
the `RealCoord` section of `ConeEulerBox`. For the cone form
$Q_w = \langle c_w\rangle\perp\langle -c_w\rangle\perp Q'_w$ at a complex place $w$ (with $c_w = \tau_w(c_0)$,
$Q'_w = Q_0'^{\tau_w}$, $\tau_w = \sigma_w$ the complex embedding), $|z|_{\mathbb C} = |z|^2$:

* **the section and the orbit section**: `QwC`, `secCx` (our section, the matrices of the section data `Dc` at
  $\sigma_w$), `orbCx` (the complex `ConeComplex.coneOrbitSection` with its section replaced by `secCx`), and the
  identification **`castCx`** : $SO(Q_0^{\sigma_w})(\mathbb C)\simeq SO(Q_w)(\mathbb C)$ (the two forms are equal,
  `QCx_eq_QwC`);
* **`lerayMeasureC_orbCx_image`**: the local fibration identity on coordinate boxes,
  $\mu_{Q_w}\big(\Psi(A\times B)\big) = |2c_w|_{\mathbb C}^{-(2k+2)}\,\sigma_C(A)\,\mu_P(B)$, $\Psi(z, p) = s(z)\,p$,
  with the constant `cCw` $= \|2c_w\|^{-2(2k+2)}$ (the complex cone orbital identity
  `ConeComplex.lerayMeasureC_cone_orbital`, whose section is irrelevant by `OrbitSection.fibMeasure_eq_of_sec`);
* **`muPC_inv_preimage`**: $\mu_P(B^{-1}) = \mu_P(B)$ ($\mu_P$ is left and right invariant, hence inversion invariant;
  the generic lemma is `map_inv_eq_of_isMulLeftRightInvariant`);
* **`muPC_pElem_image`**, **`mem_pElemC_image_iff`**: $\mu_P$ of a coordinate box
  $\{n(w')\,\mathrm{diag}(1,1,h) : w'\in W,\ h\in V\}$ is $\mathrm{vol}(W)\,\mu_{Q'_w}(V)$, and the membership criterion
  for such a box in terms of $p\,e_0$;
* **`measurable_castCx`**, **`map_castCx`**: the identification `castCx` is measurable and carries the Leray measure of
  $SO(Q_0^{\sigma_w})(\mathbb C)$ to that of $SO(Q_w)(\mathbb C)$;
* **the coordinates without the orbit-section wrapper**: `PCx`, `ofCoordCx`, `fibCx`, their inverse properties,
  `mem_ofCoordCx_image`, `lerayMeasureC_ofCoordCx_image`, `measurable_fibCx`, `measurableSet_ofCoordCx_image`.
-/

open MeasureTheory Set Matrix
open scoped ENNReal NNReal RestrictedProduct

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayComplex
  QuadFormsKB.Tamagawa.Measure.ConeAlgebra QuadFormsKB.Tamagawa.Measure.LerayReal

/-! ### Generic lemma -/

/-- **The Leray measure depends only on the form (complex).** For complex forms $Q_1 = Q_2$ and a map
$f : SO(Q_1)(\mathbb C)\to SO(Q_2)(\mathbb C)$ preserving the underlying matrices, $f_*\mu_{Q_1} = \mu_{Q_2}$. -/
theorem map_lerayMeasureC_of_eq {n : ℕ} {Q₁ Q₂ : QuadForm ℂ n} (h : Q₁ = Q₂) (h₁ : gramDetC Q₁ ≠ 0)
    (h₂ : gramDetC Q₂ ≠ 0) (f : ArchSOC Q₁ → ArchSOC Q₂)
    (hf : ∀ g, ArchSOC.mat _ (f g) = ArchSOC.mat _ g) :
    (lerayMeasureC Q₁ h₁).map f = lerayMeasureC Q₂ h₂ := by
  subst h
  have : f = id := funext fun g => by
    apply Subtype.ext; apply Units.ext; exact hf g
  rw [this, Measure.map_id]

/-! ### Complex places: the section and the identification -/

section Complex

variable {F : Type} [Field F] [NumberField F] {c₀ : 𝓞 F} {k : ℕ} {Q₀' : QuadForm (𝓞 F) k} (hc : c₀ ≠ 0)
  (hQ' : Q₀'.Nondegenerate) (hk : 3 ≤ k) (w : {w : InfinitePlace F // w.IsComplex})

local notation "QC" => ConeFinite.Qcone c₀ Q₀'

/-- The cone form at the complex place $w$: $\langle c_w\rangle\perp\langle -c_w\rangle\perp Q'_w$. -/
abbrev QwC (c₀ : 𝓞 F) (Q₀' : QuadForm (𝓞 F) k) (w : {w : InfinitePlace F // w.IsComplex}) : QuadForm ℂ (k + 1 + 1) :=
  coneForm (ConeAdelic.cCx c₀ w) (QCx Q₀' w)

/-- **The constant** $\|2c_w\|^{-2(2k+2)} = |2c_w|_{\mathbb C}^{-(2k+2)}$ of the local fibration identity at the complex
place $w$ ($|z|_{\mathbb C} = |z|^2$). -/
abbrev cCw (c₀ : 𝓞 F) (k : ℕ) (w : {w : InfinitePlace F // w.IsComplex}) : ℝ≥0∞ :=
  (((‖2 * ConeAdelic.cCx c₀ w‖₊ ^ (2 * (2 * k + 2)))⁻¹ : ℝ≥0) : ℝ≥0∞)

theorem QCx_eq_QwC : QCx QC w = QwC c₀ Q₀' w := ConeAdelic.QCx_cone w

theorem hesAt_eq_QwC : hesAt QC (σC w) = (QwC c₀ Q₀' w).hessian := hesAt_cone c₀ Q₀' (σC w)

include hc in
theorem cCx_ne : ConeAdelic.cCx c₀ w ≠ 0 := ConeAdelic.cCx_ne_zero hc w

include hQ' in
theorem gramDetC_QCx' : gramDetC (QCx Q₀' w) ≠ 0 := gramDetC_QCx_ne_zero Q₀' hQ' w

theorem qH_of_mem_coneSetC {z : Fin (k + 1 + 1) → ℂ} (hz : z ∈ ConeComplex.coneSet (QwC c₀ Q₀' w)) :
    qH (hesAt QC (σC w)) z = 0 := by
  rw [hesAt_eq_QwC]
  have h := QuadFormsKB.Siegel.Kneser.two_mul_evalIn (K := ℂ) (QwC c₀ Q₀' w) z
  rw [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] at h
  rw [qH, ← h, show QuadForm.evalIn ℂ (QwC c₀ Q₀' w) z = 0 from hz.1, mul_zero]

theorem mem_soC_QwC {g : GL (Fin (k + 1 + 1)) ℂ} (hg : IsSOAt QC (σC w) g) : g ∈ soC (QwC c₀ Q₀' w) := by
  have h : g ∈ soC (QCx QC w) := mem_soC_of QC (σC w) hg.1 hg.2
  rw [QCx_eq_QwC] at h
  exact h

/-- **The section at a complex place** $w$, $C^\circ_w\to SO(Q_w)(\mathbb C)$. -/
def secCx (z : ConeComplex.ConeT (QwC c₀ Q₀' w)) : ArchSOC (QwC c₀ Q₀' w) :=
  ArchSOC.mk _ ((Dc hc hQ' hk).secGL z.1 (qH_of_mem_coneSetC w z.2) z.2.2)
    (mem_soC_QwC w ((Dc hc hQ' hk).isSOAt_secGL (qH_of_mem_coneSetC w z.2) z.2.2))

theorem mat_secCx (z : ConeComplex.ConeT (QwC c₀ Q₀' w)) :
    ArchSOC.mat _ (secCx hc hQ' hk w z) = (Dc hc hQ' hk).secM (σC w) z.1 := rfl

theorem secCx_smul (z : ConeComplex.ConeT (QwC c₀ Q₀' w)) :
    secCx hc hQ' hk w z • ConeComplex.eCone (cCx_ne hc w) = z := by
  apply Subtype.ext
  rw [ConeComplex.coe_smul_cone, mat_secCx]
  have h := (Dc hc hQ' hk).secGL_mulVec (σ := σC w) (qH_of_mem_coneSetC w z.2) z.2.2
  rw [eAt_coneSecData] at h
  exact h

theorem measurable_secCx : Measurable (secCx hc hQ' hk w) := by
  refine measurable_archSOC_of (f := secCx hc hQ' hk w) ?_ ?_
  · exact ((Dc hc hQ' hk).measurable_secM (σC w)).comp measurable_subtype_coe
  · exact ((Dc hc hQ' hk).measurable_secMInv (σC w)).comp measurable_subtype_coe

/-- **The complex cone orbit section at $w$ with our section** (same base point and stabilizer). -/
def orbCx : OrbitSection (ArchSOC (QwC c₀ Q₀' w)) (ConeComplex.ConeT (QwC c₀ Q₀' w)) :=
  { ConeComplex.coneOrbitSection (cCx_ne hc w) (gramDetC_QCx' hQ' w)
      (OrbitalComplex.sphSectionC (neg_ne_zero.mpr (cCx_ne hc w)) (by omega : 1 ≤ k) (gramDetC_QCx' hQ' w)) with
    sec := secCx hc hQ' hk w
    sec_smul := secCx_smul hc hQ' hk w
    measurable_sec := measurable_secCx hc hQ' hk w }

/-- **The identification** $SO(Q_0^{\sigma_w})(\mathbb C)\to SO(Q_w)(\mathbb C)$ (the same matrices). -/
def castCx : ArchSOC (QCx QC w) →* ArchSOC (QwC c₀ Q₀' w) where
  toFun g := ArchSOC.mk _ (ArchSOC.incl _ g) (by
    have := AdelicSphereSetup.hes_of_mem_soC QC (σC w) g.2
    exact mem_soC_QwC w this)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem mat_castCx (g : ArchSOC (QCx QC w)) : ArchSOC.mat _ (castCx w g) = ArchSOC.mat _ g := rfl

theorem castCx_injective : Function.Injective (castCx (c₀ := c₀) (Q₀' := Q₀') w) := fun _ _ e =>
  Subtype.ext (congrArg (fun x : ArchSOC (QwC c₀ Q₀' w) => (ArchSOC.incl _ x : GL (Fin (k + 1 + 1)) ℂ)) e)

theorem castCx_surjective : Function.Surjective (castCx (c₀ := c₀) (Q₀' := Q₀') w) := fun g =>
  ⟨ArchSOC.mk _ (ArchSOC.incl _ g) (by
    rw [QCx_eq_QwC w]
    exact g.2), rfl⟩

/-! ### Local facts: the fibration identity, $\mu_P$, and `castCx` -/

/-- **The local fibration identity on coordinate boxes** at the complex place $w$: for measurable
$A\subseteq C^\circ_w$ and $B\subseteq P_w$,
$$\mu_{Q_w}\big(\{s(z)\,p : z\in A,\ p\in B\}\big) = \|2c_w\|^{-2(2k+2)}\,\sigma_C(A)\,\mu_P(B),$$
with $s$ our section `secCx` (the complex cone orbital identity `ConeComplex.lerayMeasureC_cone_orbital` is
independent of the section by `OrbitSection.fibMeasure_eq_of_sec`). -/
theorem lerayMeasureC_orbCx_image {A : Set (ConeComplex.ConeT (QwC c₀ Q₀' w))} (hA : MeasurableSet A)
    {B : Set (orbCx hc hQ' hk w).stab} (hB : MeasurableSet B) :
    lerayMeasureC (QwC c₀ Q₀' w) (ConeComplex.gramDetC_cone (cCx_ne hc w) (gramDetC_QCx' hQ' w))
        ((orbCx hc hQ' hk w).ofCoord '' (A ×ˢ B)) =
      cCw c₀ k w * ConeComplex.sigCone (cCx_ne hc w) A *
        ConeComplex.muP (cCx_ne hc w) (gramDetC_QCx' hQ' w) B := by
  have hmeas : MeasurableSet ((orbCx hc hQ' hk w).ofCoord '' (A ×ˢ B)) :=
    (orbCx hc hQ' hk w).coordEquiv.symm.measurableEmbedding.measurableSet_image.2 (hA.prod hB)
  have hpre : (orbCx hc hQ' hk w).ofCoord ⁻¹' ((orbCx hc hQ' hk w).ofCoord '' (A ×ˢ B)) = A ×ˢ B :=
    ((orbCx hc hQ' hk w).coordEquiv.symm.injective : Function.Injective (orbCx hc hQ' hk w).ofCoord).preimage_image _
  have h := ConeComplex.lerayMeasureC_cone_orbital (cCx_ne hc w) (gramDetC_QCx' hQ' w)
    (OrbitalComplex.sphSectionC (neg_ne_zero.mpr (cCx_ne hc w)) (by omega : 1 ≤ k) (gramDetC_QCx' hQ' w))
  have e : (orbCx hc hQ' hk w).fibMeasure (ConeComplex.sigCone (cCx_ne hc w))
        (ConeComplex.muP (cCx_ne hc w) (gramDetC_QCx' hQ' w)) =
      (ConeComplex.coneOrbitSection (cCx_ne hc w) (gramDetC_QCx' hQ' w)
        (OrbitalComplex.sphSectionC (neg_ne_zero.mpr (cCx_ne hc w)) (by omega : 1 ≤ k)
          (gramDetC_QCx' hQ' w))).fibMeasure
        (ConeComplex.sigCone (cCx_ne hc w)) (ConeComplex.muP (cCx_ne hc w) (gramDetC_QCx' hQ' w)) :=
    OrbitSection.fibMeasure_eq_of_sec _ _ _ _ _ _
  have : SFinite (α := (orbCx hc hQ' hk w).stab) (ConeComplex.muP (cCx_ne hc w) (gramDetC_QCx' hQ' w)) :=
    inferInstanceAs (SFinite (ConeComplex.muP (cCx_ne hc w) (gramDetC_QCx' hQ' w)))
  have h3 := (orbCx hc hQ' hk w).fibMeasure_apply (ConeComplex.sigCone (cCx_ne hc w))
    (ConeComplex.muP (cCx_ne hc w) (gramDetC_QCx' hQ' w)) hmeas
  have h4 := Measure.prod_prod (μ := ConeComplex.sigCone (cCx_ne hc w))
    (ν := ConeComplex.muP (cCx_ne hc w) (gramDetC_QCx' hQ' w)) A
    (B : Set (ConeComplex.stabP (Q' := QCx Q₀' w) (cCx_ne hc w)))
  rw [h, Measure.smul_apply, ← e, h3, hpre]
  exact (congrArg (fun x => cCw c₀ k w • x) h4).trans (by rw [smul_eq_mul, mul_assoc])

include hc hQ' in
theorem muPC_inv_preimage_aux {B : Set (ConeComplex.stabP (Q' := QCx Q₀' w) (cCx_ne hc w))} (hB : MeasurableSet B) :
    ConeComplex.muP (cCx_ne hc w) (gramDetC_QCx' hQ' w) ((fun p => p⁻¹) ⁻¹' B) =
      ConeComplex.muP (cCx_ne hc w) (gramDetC_QCx' hQ' w) B := by
  obtain ⟨U, hU, hU0, hUt⟩ := OrbitSection.exists_pos_lt_top
    (ConeComplex.muP (cCx_ne hc w) (gramDetC_QCx' hQ' w)) (ConeComplex.muP_ne_zero _ _)
  have := map_inv_eq_of_isMulLeftRightInvariant (ConeComplex.muP (cCx_ne hc w) (gramDetC_QCx' hQ' w)) hU0 hUt
  have h2 := congrArg (fun m => m B) this
  exact (Measure.map_apply measurable_inv hB).symm.trans h2

include hc hQ' in
/-- **$\mu_P$ is invariant under inversion** ($P$ is unimodular: $\mu_P$ is left and right invariant). -/
theorem muPC_inv_preimage {B : Set (orbCx hc hQ' hk w).stab} (hB : MeasurableSet B) :
    ConeComplex.muP (cCx_ne hc w) (gramDetC_QCx' hQ' w) ((fun p => p⁻¹) ⁻¹' B) =
      ConeComplex.muP (cCx_ne hc w) (gramDetC_QCx' hQ' w) B :=
  muPC_inv_preimage_aux hc hQ' w hB

/-- **$\mu_P$ of a coordinate box**: $\mu_P\big(\{n(w')\mathrm{diag}(1,1,h) : w'\in W,\ h\in V\}\big) =
\mathrm{vol}(W)\,\mu_{Q'_w}(V)$. -/
theorem muPC_pElem_image {W : Set (Fin k → ℂ)} (_hW : MeasurableSet W) {V : Set (ArchSOC (QCx Q₀' w))}
    (_hV : MeasurableSet V) :
    ConeComplex.muP (cCx_ne hc w) (gramDetC_QCx' hQ' w)
        (ConeComplex.pElem (cCx_ne hc w) (gramDetC_QCx' hQ' w) '' (W ×ˢ V)) =
      volume W * lerayMeasureC (QCx Q₀' w) (gramDetC_QCx' hQ' w) V := by
  have := isHaarMeasure_lerayMeasureC (gramDetC_QCx' hQ' w)
  rw [ConeComplex.muP, (ConeComplex.measurableEmbedding_pElem (cCx_ne hc w) (gramDetC_QCx' hQ' w)).map_apply,
    (ConeComplex.pElem_injective (cCx_ne hc w) (gramDetC_QCx' hQ' w)).preimage_image, Measure.prod_prod]

theorem mat_pElemC (x : (Fin k → ℂ) × ArchSOC (QCx Q₀' w)) :
    ArchSOC.mat _ ((ConeComplex.pElem (cCx_ne hc w) (gramDetC_QCx' hQ' w) x : (orbCx hc hQ' hk w).stab) :
        ArchSOC (QwC c₀ Q₀' w)) =
      nM (ConeAdelic.cCx c₀ w) (QCx Q₀' w) x.1 * mM (ArchSOC.mat _ x.2) := by
  show ArchSOC.mat _ (ConeComplex.nG (cCx_ne hc w) (gramDetC_QCx' hQ' w) x.1 *
    ConeComplex.mG (ConeAdelic.cCx c₀ w) (QCx Q₀' w) x.2) = _
  rw [ArchSOC.mat_mul, ConeComplex.mat_nG, ConeComplex.mat_mG]

/-- **Membership in a coordinate box of $P$**: $p = n(w')\mathrm{diag}(1,1,h)$ with $w'\in W$, $h\in V$ iff
$(p\,e_0)'\in W$ and $\mathrm{diag}(1,1,h) = n(-(p\,e_0)')\,p$ for some $h\in V$. -/
theorem mem_pElemC_image_iff {W : Set (Fin k → ℂ)} {V : Set (ArchSOC (QCx Q₀' w))}
    (p : (orbCx hc hQ' hk w).stab) :
    p ∈ ConeComplex.pElem (cCx_ne hc w) (gramDetC_QCx' hQ' w) '' (W ×ˢ V) ↔
      ConeAlgebra.tl (ArchSOC.mat _ (p : ArchSOC (QwC c₀ Q₀' w)) *ᵥ e₀) ∈ W ∧
        ∃ h ∈ V, ConeAlgebra.mM (ArchSOC.mat _ h) =
          ConeAlgebra.nM (ConeAdelic.cCx c₀ w) (QCx Q₀' w)
            (-ConeAlgebra.tl (ArchSOC.mat _ (p : ArchSOC (QwC c₀ Q₀' w)) *ᵥ e₀)) *
              ArchSOC.mat _ (p : ArchSOC (QwC c₀ Q₀' w)) := by
  have hcw := cCx_ne hc w
  constructor
  · rintro ⟨⟨w', h⟩, ⟨hw', hh⟩, rfl⟩
    have hm := mat_pElemC hc hQ' w (w', h)
    have htl : ConeAlgebra.tl (ArchSOC.mat _ ((ConeComplex.pElem (cCx_ne hc w) (gramDetC_QCx' hQ' w) (w', h) :
        (orbCx hc hQ' hk w).stab) : ArchSOC (QwC c₀ Q₀' w)) *ᵥ e₀) = w' := by
      rw [hm, ← mulVec_mulVec, mM_mulVec_e₀, tl_nM_mulVec_e₀ _ _ hcw]
    refine ⟨by rw [htl]; exact hw', h, hh, ?_⟩
    rw [htl, hm, ← mul_assoc, nM_mul _ _ hcw, neg_add_cancel, nM_zero, one_mul]
  · rintro ⟨hW, h, hh, he⟩
    set w' := ConeAlgebra.tl (ArchSOC.mat _ (p : ArchSOC (QwC c₀ Q₀' w)) *ᵥ e₀)
    refine ⟨(w', h), ⟨hW, hh⟩, ?_⟩
    apply Subtype.ext
    apply ConeComplex.mat_ext'
    have hm := mat_pElemC hc hQ' w (w', h)
    rw [hm, he, ← mul_assoc, nM_mul _ _ hcw, add_neg_cancel, nM_zero, one_mul]

/-- **$\mathrm{castCx}$ is measurable.** -/
theorem measurable_castCx : Measurable (castCx (c₀ := c₀) (Q₀' := Q₀') w) := by
  refine measurable_archSOC_of (f := castCx (c₀ := c₀) (Q₀' := Q₀') w) ?_ ?_
  · exact (Units.continuous_val.comp (ArchSOC.continuous_incl _)).measurable
  · have : (fun g : ArchSOC (QCx QC w) =>
        (((ArchSOC.incl _ (castCx (c₀ := c₀) (Q₀' := Q₀') w g))⁻¹ : GL (Fin (k + 1 + 1)) ℂ) :
          Matrix (Fin (k + 1 + 1)) (Fin (k + 1 + 1)) ℂ)) =
        fun g => (((ArchSOC.incl _ g)⁻¹ : GL (Fin (k + 1 + 1)) ℂ) : Matrix (Fin (k + 1 + 1)) (Fin (k + 1 + 1)) ℂ) :=
      rfl
    rw [this]
    exact (Units.continuous_val.comp (continuous_inv.comp (ArchSOC.continuous_incl _))).measurable

include hc hQ' in
/-- **`castCx` carries the Leray measure of $SO(Q_0^{\sigma_w})(\mathbb C)$ to that of $SO(Q_w)(\mathbb C)$** (the two
forms are equal, `QCx_eq_QwC`, and `castCx` preserves the matrices). -/
theorem map_castCx :
    (lerayMeasureC (QCx (ConeFinite.Qcone c₀ Q₀') w)
      (gramDetC_QCx_ne_zero (ConeFinite.Qcone c₀ Q₀') (ConeFinite.nondeg_cone c₀ Q₀' hc hQ') w)).map (castCx w) =
    lerayMeasureC (QwC c₀ Q₀' w) (ConeComplex.gramDetC_cone (cCx_ne hc w) (gramDetC_QCx' hQ' w)) :=
  map_lerayMeasureC_of_eq (QCx_eq_QwC w) _ _ (castCx w) (mat_castCx w)

/-! ### Complex-place coordinates without the orbit-section wrapper -/

/-- The stabilizer $P_w$ of $e$ in $SO(Q_w)(\mathbb C)$. -/
abbrev PCx (Q₀' : QuadForm (𝓞 F) k) (hc : c₀ ≠ 0) (w : {w : InfinitePlace F // w.IsComplex}) :
    Subgroup (ArchSOC (QwC c₀ Q₀' w)) := ConeComplex.stabP (Q' := QCx Q₀' w) (cCx_ne hc w)

/-- Our coordinates $(z, p)\mapsto s(z)\,p$ at the complex place $w$. -/
def ofCoordCx (q : ConeComplex.ConeT (QwC c₀ Q₀' w) × PCx Q₀' hc w) : ArchSOC (QwC c₀ Q₀' w) :=
  secCx hc hQ' hk w q.1 * (q.2 : ArchSOC (QwC c₀ Q₀' w))

/-- The fibre coordinate $g\mapsto s(ge)^{-1}g$ at the complex place $w$. -/
def fibCx (g : ArchSOC (QwC c₀ Q₀' w)) : PCx Q₀' hc w :=
  ⟨(secCx hc hQ' hk w (g • ConeComplex.eCone (cCx_ne hc w)))⁻¹ * g, by
    rw [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff]
    exact (secCx_smul hc hQ' hk w _).symm⟩

theorem ofCoordCx_smul (q : ConeComplex.ConeT (QwC c₀ Q₀' w) × PCx Q₀' hc w) :
    ofCoordCx hc hQ' hk w q • ConeComplex.eCone (cCx_ne hc w) = q.1 := by
  have hp : (q.2 : ArchSOC (QwC c₀ Q₀' w)) • ConeComplex.eCone (cCx_ne hc w) = ConeComplex.eCone (cCx_ne hc w) :=
    q.2.2
  rw [ofCoordCx, mul_smul, hp, secCx_smul]

theorem ofCoordCx_fibCx (g : ArchSOC (QwC c₀ Q₀' w)) :
    ofCoordCx hc hQ' hk w (g • ConeComplex.eCone (cCx_ne hc w), fibCx hc hQ' hk w g) = g := by
  simp [ofCoordCx, fibCx]

theorem fibCx_ofCoordCx (q : ConeComplex.ConeT (QwC c₀ Q₀' w) × PCx Q₀' hc w) :
    fibCx hc hQ' hk w (ofCoordCx hc hQ' hk w q) = q.2 := by
  apply Subtype.ext
  simp only [fibCx, ofCoordCx_smul]
  simp [ofCoordCx]

theorem mem_ofCoordCx_image {A : Set (ConeComplex.ConeT (QwC c₀ Q₀' w))} {B : Set (PCx Q₀' hc w)}
    (g : ArchSOC (QwC c₀ Q₀' w)) :
    g ∈ ofCoordCx hc hQ' hk w '' (A ×ˢ B) ↔
      g • ConeComplex.eCone (cCx_ne hc w) ∈ A ∧ fibCx hc hQ' hk w g ∈ B := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [ofCoordCx_smul, fibCx_ofCoordCx]; exact hq
  · rintro ⟨h1, h2⟩
    exact ⟨_, ⟨h1, h2⟩, ofCoordCx_fibCx hc hQ' hk w g⟩

theorem lerayMeasureC_ofCoordCx_image {A : Set (ConeComplex.ConeT (QwC c₀ Q₀' w))} (hA : MeasurableSet A)
    {B : Set (PCx Q₀' hc w)} (hB : MeasurableSet B) :
    lerayMeasureC (QwC c₀ Q₀' w) (ConeComplex.gramDetC_cone (cCx_ne hc w) (gramDetC_QCx' hQ' w))
        (ofCoordCx hc hQ' hk w '' (A ×ˢ B)) =
      cCw c₀ k w * ConeComplex.sigCone (cCx_ne hc w) A *
        ConeComplex.muP (cCx_ne hc w) (gramDetC_QCx' hQ' w) B :=
  lerayMeasureC_orbCx_image hc hQ' hk w hA hB

theorem measurable_fibCx : Measurable (fibCx hc hQ' hk w) := by
  have hsm : Measurable fun g : ArchSOC (QwC c₀ Q₀' w) => g • ConeComplex.eCone (cCx_ne hc w) :=
    ((ConeComplex.continuous_smul_cone _).comp (continuous_id.prodMk continuous_const)).measurable
  exact Measurable.subtype_mk (((measurable_secCx hc hQ' hk w).comp hsm).inv.mul measurable_id)

theorem measurableSet_ofCoordCx_image {A : Set (ConeComplex.ConeT (QwC c₀ Q₀' w))} (hA : MeasurableSet A)
    {B : Set (PCx Q₀' hc w)} (hB : MeasurableSet B) :
    MeasurableSet (ofCoordCx hc hQ' hk w '' (A ×ˢ B)) := by
  have hsm : Measurable fun g : ArchSOC (QwC c₀ Q₀' w) => g • ConeComplex.eCone (cCx_ne hc w) :=
    ((ConeComplex.continuous_smul_cone _).comp (continuous_id.prodMk continuous_const)).measurable
  have : ofCoordCx hc hQ' hk w '' (A ×ˢ B) = (fun g => g • ConeComplex.eCone (cCx_ne hc w)) ⁻¹' A ∩
      fibCx hc hQ' hk w ⁻¹' B := by
    ext g; rw [mem_ofCoordCx_image]; rfl
  rw [this]
  exact (hsm hA).inter (measurable_fibCx hc hQ' hk w hB)

end Complex

end QuadFormsKB.Tamagawa.Measure.Weil

end
