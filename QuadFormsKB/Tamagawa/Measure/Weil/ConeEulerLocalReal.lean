import QuadFormsKB.Tamagawa.Measure.Weil.ConeEulerBase

/-!
# Local facts at a real place for the cone form

For the cone form $Q_w = \langle c_w\rangle\perp\langle -c_w\rangle\perp Q'_w$ at a real place $w$ (the notation of
`ConeEulerBase`), with the orbit section `orbR` (our section `secR`, base point $e$, stabilizer $P$):

* **`lerayMeasure_orbR_image`**: the local fibration identity on coordinate boxes,
  $\mu_{Q_w}\big(\Psi(A\times B)\big) = |2c_w|^{-(2k+2)}\,\sigma_C(A)\,\mu_P(B)$, $\Psi(z, p) = s(z)\,p$
  (the cone orbital identity `ConeReal.lerayMeasure_cone_orbital`, whose section is irrelevant by
  `OrbitSection.fibMeasure_eq_of_sec`);
* **`muP_inv_preimage`**: $\mu_P(B^{-1}) = \mu_P(B)$ ($\mu_P$ is left and right invariant, hence inversion invariant;
  the generic lemma is `map_inv_eq_of_isMulLeftRightInvariant`);
* **`muP_pElem_image`**, **`mem_pElem_image_iff`**: $\mu_P$ of a coordinate box
  $\{n(w')\,\mathrm{diag}(1,1,h) : w'\in W,\ h\in V\}$ is $\mathrm{vol}(W)\,\mu_{Q'_w}(V)$, and the membership criterion
  for such a box in terms of $p\,e_0$;
* **`measurable_castR`**, **`map_castR`**: the identification `castR` of $SO(Q_0^{\sigma_w})(\mathbb R)$ with
  $SO(Q_w)(\mathbb R)$ is measurable and carries the Leray measure of the former to that of the latter.
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

/-! ### Generic lemmas -/

/-- **A left and right invariant measure is inversion invariant.** If $\mu$ is σ-finite, left and right invariant on a
group with measurable multiplication and inversion, and $0 < \mu(U) < \infty$ for some $U$, then
$\mu(B^{-1}) = \mu(B)$, i.e. $(g\mapsto g^{-1})_*\mu = \mu$. (Proof: $\mu^{-1}$ is left invariant, so $\mu^{-1} = c\mu$;
applying inversion twice gives $c^2 = 1$.) -/
theorem map_inv_eq_of_isMulLeftRightInvariant {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    [MeasurableInv G] (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {U : Set G}
    (h0 : μ U ≠ 0) (htop : μ U ≠ ∞) : μ.map (fun g => g⁻¹) = μ := by
  have hc := measure_eq_div_smul μ.inv μ h0 htop
  set c := μ.inv U / μ U
  have h2 : μ = (c * c) • μ := by
    conv_lhs => rw [← Measure.inv_inv μ, hc]
    rw [Measure.inv_def, Measure.map_smul _ measurable_inv.aemeasurable, ← Measure.inv_def, hc, smul_smul]
  have h3 : (c * c) * μ U = 1 * μ U := by
    conv_rhs => rw [one_mul, h2]
    rfl
  have h4 : c * c = 1 := (ENNReal.mul_left_inj h0 htop).1 h3
  have h5 : c = 1 := by
    have hc0 : c ≠ ⊤ := by
      rintro h; rw [h] at h4; simp at h4
    clear_value c
    lift c to ℝ≥0 using hc0
    have h6 : (c : ℝ) * c = 1 := by exact_mod_cast h4
    have h7 : ((c : ℝ) - 1) * ((c : ℝ) + 1) = 0 := by linear_combination h6
    have h8 : (c : ℝ) + 1 ≠ 0 := by positivity
    have h9 : (c : ℝ) = 1 := by linarith [(mul_eq_zero.mp h7).resolve_right h8]
    have : c = 1 := by exact_mod_cast h9
    simp [this]
  rw [← Measure.inv_def, hc, h5, one_smul]

/-- **The Leray measure depends only on the form.** For real forms $Q_1 = Q_2$ and a map
$f : SO(Q_1)(\mathbb R)\to SO(Q_2)(\mathbb R)$ preserving the underlying matrices, $f_*\mu_{Q_1} = \mu_{Q_2}$. -/
theorem map_lerayMeasure_of_eq {n : ℕ} {Q₁ Q₂ : QuadForm ℝ n} (h : Q₁ = Q₂) (h₁ : Siegel.gramDetR Q₁ ≠ 0)
    (h₂ : Siegel.gramDetR Q₂ ≠ 0) (f : ArchSO Q₁ → ArchSO Q₂)
    (hf : ∀ g, ArchSOInst.mat _ (f g) = ArchSOInst.mat _ g) :
    (lerayMeasure Q₁ h₁).map f = lerayMeasure Q₂ h₂ := by
  subst h
  have : f = id := funext fun g => by
    apply Subtype.ext; apply Units.ext; exact hf g
  rw [this, Measure.map_id]

/-! ### Real places -/

section Real

variable {F : Type} [Field F] [NumberField F] {c₀ : 𝓞 F} {k : ℕ} {Q₀' : QuadForm (𝓞 F) k} (hc : c₀ ≠ 0)
  (hQ' : Q₀'.Nondegenerate) (hk : 3 ≤ k) (w : {w : InfinitePlace F // w.IsReal})

local notation "QC" => ConeFinite.Qcone c₀ Q₀'

/-- **The local fibration identity on coordinate boxes** at the real place $w$: for measurable $A\subseteq C^\circ_w$ and
$B\subseteq P_w$,
$$\mu_{Q_w}\big(\{s(z)\,p : z\in A,\ p\in B\}\big) = |2c_w|^{-(2k+2)}\,\sigma_C(A)\,\mu_P(B),$$
with $s$ our section `secR` (the cone orbital identity `ConeReal.lerayMeasure_cone_orbital` is independent of the
section by `OrbitSection.fibMeasure_eq_of_sec`). -/
theorem lerayMeasure_orbR_image {A : Set (ConeReal.ConeT (Qw c₀ Q₀' w))} (hA : MeasurableSet A)
    {B : Set (orbR hc hQ' hk w).stab} (hB : MeasurableSet B) :
    lerayMeasure (Qw c₀ Q₀' w) (ConeReal.gramDetR_cone (cRe_ne hc w) (gramDetR_QRe' hQ' w))
        ((orbR hc hQ' hk w).ofCoord '' (A ×ˢ B)) =
      ENNReal.ofReal ((|2 * ConeAdelic.cRe c₀ w| ^ (2 * k + 2))⁻¹) * ConeReal.sigCone (cRe_ne hc w) A *
        ConeReal.muP (cRe_ne hc w) (gramDetR_QRe' hQ' w) B := by
  have hmeas : MeasurableSet ((orbR hc hQ' hk w).ofCoord '' (A ×ˢ B)) :=
    (orbR hc hQ' hk w).coordEquiv.symm.measurableEmbedding.measurableSet_image.2 (hA.prod hB)
  have hpre : (orbR hc hQ' hk w).ofCoord ⁻¹' ((orbR hc hQ' hk w).ofCoord '' (A ×ˢ B)) = A ×ˢ B :=
    ((orbR hc hQ' hk w).coordEquiv.symm.injective : Function.Injective (orbR hc hQ' hk w).ofCoord).preimage_image _
  have h := ConeReal.lerayMeasure_cone_orbital (cRe_ne hc w) (gramDetR_QRe' hQ' w)
    (OrbitalReal.sphSection (neg_ne_zero.mpr (cRe_ne hc w)) (by omega : 1 ≤ k) (gramDetR_QRe' hQ' w))
  have e : (orbR hc hQ' hk w).fibMeasure (ConeReal.sigCone (cRe_ne hc w))
        (ConeReal.muP (cRe_ne hc w) (gramDetR_QRe' hQ' w)) =
      (ConeReal.coneOrbitSection (cRe_ne hc w) (gramDetR_QRe' hQ' w)
        (OrbitalReal.sphSection (neg_ne_zero.mpr (cRe_ne hc w)) (by omega : 1 ≤ k) (gramDetR_QRe' hQ' w))).fibMeasure
        (ConeReal.sigCone (cRe_ne hc w)) (ConeReal.muP (cRe_ne hc w) (gramDetR_QRe' hQ' w)) :=
    OrbitSection.fibMeasure_eq_of_sec _ _ _ _ _ _
  have : SFinite (α := (orbR hc hQ' hk w).stab) (ConeReal.muP (cRe_ne hc w) (gramDetR_QRe' hQ' w)) :=
    inferInstanceAs (SFinite (ConeReal.muP (cRe_ne hc w) (gramDetR_QRe' hQ' w)))
  have h3 := (orbR hc hQ' hk w).fibMeasure_apply (ConeReal.sigCone (cRe_ne hc w))
    (ConeReal.muP (cRe_ne hc w) (gramDetR_QRe' hQ' w)) hmeas
  have h4 := Measure.prod_prod (μ := ConeReal.sigCone (cRe_ne hc w))
    (ν := ConeReal.muP (cRe_ne hc w) (gramDetR_QRe' hQ' w)) A
    (B : Set (ConeReal.stabP (Q' := QRe Q₀' w) (cRe_ne hc w)))
  rw [h, Measure.smul_apply, ← e, h3, hpre]
  exact (congrArg (fun x => ENNReal.ofReal ((|2 * ConeAdelic.cRe c₀ w| ^ (2 * k + 2))⁻¹) • x) h4).trans
    (by rw [smul_eq_mul, mul_assoc])

include hc hQ' in
theorem muP_inv_preimage_aux {B : Set (ConeReal.stabP (Q' := QRe Q₀' w) (cRe_ne hc w))} (hB : MeasurableSet B) :
    ConeReal.muP (cRe_ne hc w) (gramDetR_QRe' hQ' w) ((fun p => p⁻¹) ⁻¹' B) =
      ConeReal.muP (cRe_ne hc w) (gramDetR_QRe' hQ' w) B := by
  obtain ⟨U, hU, hU0, hUt⟩ := OrbitSection.exists_pos_lt_top
    (ConeReal.muP (cRe_ne hc w) (gramDetR_QRe' hQ' w)) (ConeReal.muP_ne_zero _ _)
  have := map_inv_eq_of_isMulLeftRightInvariant (ConeReal.muP (cRe_ne hc w) (gramDetR_QRe' hQ' w)) hU0 hUt
  have h2 := congrArg (fun m => m B) this
  exact (Measure.map_apply measurable_inv hB).symm.trans h2

include hc hQ' in
/-- **$\mu_P$ is invariant under inversion** ($P$ is unimodular: $\mu_P$ is left and right invariant). -/
theorem muP_inv_preimage {B : Set (orbR hc hQ' hk w).stab} (hB : MeasurableSet B) :
    ConeReal.muP (cRe_ne hc w) (gramDetR_QRe' hQ' w) ((fun p => p⁻¹) ⁻¹' B) =
      ConeReal.muP (cRe_ne hc w) (gramDetR_QRe' hQ' w) B :=
  muP_inv_preimage_aux hc hQ' w hB

/-- **$\mu_P$ of a coordinate box**: $\mu_P\big(\{n(w')\mathrm{diag}(1,1,h) : w'\in W,\ h\in V\}\big) =
\mathrm{vol}(W)\,\mu_{Q'_w}(V)$. -/
theorem muP_pElem_image {W : Set (Fin k → ℝ)} (_hW : MeasurableSet W) {V : Set (ArchSO (QRe Q₀' w))}
    (_hV : MeasurableSet V) :
    ConeReal.muP (cRe_ne hc w) (gramDetR_QRe' hQ' w)
        (ConeReal.pElem (cRe_ne hc w) (gramDetR_QRe' hQ' w) '' (W ×ˢ V)) =
      volume W * lerayMeasure (QRe Q₀' w) (gramDetR_QRe' hQ' w) V := by
  have := isHaarMeasure_lerayMeasure (gramDetR_QRe' hQ' w)
  rw [ConeReal.muP, (ConeReal.measurableEmbedding_pElem (cRe_ne hc w) (gramDetR_QRe' hQ' w)).map_apply,
    (ConeReal.pElem_injective (cRe_ne hc w) (gramDetR_QRe' hQ' w)).preimage_image, Measure.prod_prod]

theorem mat_pElem (x : (Fin k → ℝ) × ArchSO (QRe Q₀' w)) :
    ArchSOInst.mat _ ((ConeReal.pElem (cRe_ne hc w) (gramDetR_QRe' hQ' w) x : (orbR hc hQ' hk w).stab) :
        ArchSO (Qw c₀ Q₀' w)) =
      nM (ConeAdelic.cRe c₀ w) (QRe Q₀' w) x.1 * mM (ArchSOInst.mat _ x.2) := by
  show ArchSOInst.mat _ (ConeReal.nG (cRe_ne hc w) (gramDetR_QRe' hQ' w) x.1 *
    ConeReal.mG (ConeAdelic.cRe c₀ w) (QRe Q₀' w) x.2) = _
  rw [ArchSOInst.mat_mul, ConeReal.mat_nG, ConeReal.mat_mG]

/-- **Membership in a coordinate box of $P$**: $p = n(w')\mathrm{diag}(1,1,h)$ with $w'\in W$, $h\in V$ iff
$(p\,e_0)'\in W$ and $\mathrm{diag}(1,1,h) = n(-(p\,e_0)')\,p$ for some $h\in V$. -/
theorem mem_pElem_image_iff {W : Set (Fin k → ℝ)} {V : Set (ArchSO (QRe Q₀' w))}
    (p : (orbR hc hQ' hk w).stab) :
    p ∈ ConeReal.pElem (cRe_ne hc w) (gramDetR_QRe' hQ' w) '' (W ×ˢ V) ↔
      ConeAlgebra.tl (ArchSOInst.mat _ (p : ArchSO (Qw c₀ Q₀' w)) *ᵥ e₀) ∈ W ∧
        ∃ h ∈ V, ConeAlgebra.mM (ArchSOInst.mat _ h) =
          ConeAlgebra.nM (ConeAdelic.cRe c₀ w) (QRe Q₀' w)
            (-ConeAlgebra.tl (ArchSOInst.mat _ (p : ArchSO (Qw c₀ Q₀' w)) *ᵥ e₀)) *
              ArchSOInst.mat _ (p : ArchSO (Qw c₀ Q₀' w)) := by
  have hcw := cRe_ne hc w
  constructor
  · rintro ⟨⟨w', h⟩, ⟨hw', hh⟩, rfl⟩
    have hm := mat_pElem hc hQ' w (w', h)
    have htl : ConeAlgebra.tl (ArchSOInst.mat _ ((ConeReal.pElem (cRe_ne hc w) (gramDetR_QRe' hQ' w) (w', h) :
        (orbR hc hQ' hk w).stab) : ArchSO (Qw c₀ Q₀' w)) *ᵥ e₀) = w' := by
      rw [hm, ← mulVec_mulVec, mM_mulVec_e₀, tl_nM_mulVec_e₀ _ _ hcw]
    refine ⟨by rw [htl]; exact hw', h, hh, ?_⟩
    rw [htl, hm, ← mul_assoc, nM_mul _ _ hcw, neg_add_cancel, nM_zero, one_mul]
  · rintro ⟨hW, h, hh, he⟩
    set w' := ConeAlgebra.tl (ArchSOInst.mat _ (p : ArchSO (Qw c₀ Q₀' w)) *ᵥ e₀)
    refine ⟨(w', h), ⟨hW, hh⟩, ?_⟩
    apply Subtype.ext
    apply ConeReal.mat_ext'
    have hm := mat_pElem hc hQ' w (w', h)
    rw [hm, he, ← mul_assoc, nM_mul _ _ hcw, add_neg_cancel, nM_zero, one_mul]

/-- **$\mathrm{castR}$ is measurable.** -/
theorem measurable_castR : Measurable (castR (c₀ := c₀) (Q₀' := Q₀') w) := by
  refine measurable_archSO_of (f := castR (c₀ := c₀) (Q₀' := Q₀') w) ?_ ?_
  · exact (Units.continuous_val.comp (ArchSO.continuous_incl _)).measurable
  · have : (fun g : ArchSO (QRe QC w) =>
        (((ArchSO.incl _ (castR (c₀ := c₀) (Q₀' := Q₀') w g))⁻¹ : GL (Fin (k + 1 + 1)) ℝ) :
          Matrix (Fin (k + 1 + 1)) (Fin (k + 1 + 1)) ℝ)) =
        fun g => (((ArchSO.incl _ g)⁻¹ : GL (Fin (k + 1 + 1)) ℝ) : Matrix (Fin (k + 1 + 1)) (Fin (k + 1 + 1)) ℝ) :=
      rfl
    rw [this]
    exact (Units.continuous_val.comp (continuous_inv.comp (ArchSO.continuous_incl _))).measurable

include hc hQ' in
/-- **`castR` carries the Leray measure of $SO(Q_0^{\sigma_w})(\mathbb R)$ to that of $SO(Q_w)(\mathbb R)$** (the two
forms are equal, `QRe_eq_Qw`, and `castR` preserves the matrices). -/
theorem map_castR :
    (lerayMeasure (QRe (ConeFinite.Qcone c₀ Q₀') w)
      (gramDetR_QRe_ne_zero (ConeFinite.Qcone c₀ Q₀') (ConeFinite.nondeg_cone c₀ Q₀' hc hQ') w)).map (castR w) =
    lerayMeasure (Qw c₀ Q₀' w) (ConeReal.gramDetR_cone (cRe_ne hc w) (gramDetR_QRe' hQ' w)) :=
  map_lerayMeasure_of_eq (QRe_eq_Qw w) _ _ (castR w) (mat_castR w)

end Real

end QuadFormsKB.Tamagawa.Measure.Weil

end
