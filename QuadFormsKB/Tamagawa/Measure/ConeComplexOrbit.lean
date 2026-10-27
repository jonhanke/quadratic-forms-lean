import QuadFormsKB.Tamagawa.Measure.ConeComplex

/-!
# The cone orbital identity at a complex place

The complex analogue of `ConeRealOrbit.lean`. For $Q = \langle c\rangle\perp\langle -c\rangle\perp Q'$ over $\mathbb C$
(`coneForm c Q'`, $Q'$ nondegenerate in $k \ge 1$ variables) and $e = e_0 + e_1$, with $|z|_{\mathbb C} = |z|^2$:

* `ConeT Q`: the punctured cone $C^\circ = \{Q = 0\}\setminus 0 \subset \mathbb C^{k+2}$ with the action of $SO(Q)(\mathbb C)$;
* `sigCone hc`: the Leray measure of the cone, the image of $|q|_{\mathbb C}^{k-1}d^2q \otimes \sigma'_{-c}$ under
  $(q, y) \mapsto q(1, y)$ ($\sigma'_{-c}$ = `sigC` for $\langle -c\rangle\perp Q'$);
* `coneOrbitSection`: an explicit measurable section of $g \mapsto ge$ (`OrbitSection`);
* `muP`: the Haar measure $d^2w\otimes\mu_{Q'}$ of $P = \mathrm{Stab}(e) = N \rtimes SO(Q')$ (`exists_pElem`),
  bi-invariant (`isMulLeftInvariant_muP`, `isMulRightInvariant_muP`: $P$ is unimodular);
* **`lerayMeasureC_cone_orbital`**: $\mu_Q = |2c|_{\mathbb C}^{-2(k+1)}\cdot\Psi_*(\sigma_C \otimes \mu_P)$;
* `map_smul_sigCone`: $SO(Q)(\mathbb C)$-invariance of $\sigma_C$; `map_coneScale_sigCone`: homogeneity,
  $\sigma_C(aA) = |a|_{\mathbb C}^{k}\sigma_C(A)$.
-/

open MeasureTheory Measure Matrix Set Filter Topology
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.ConeComplex

open QuadFormsKB QuadFormsKB.Siegel QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.ArchVol
open QuadFormsKB.Tamagawa.Measure.LerayComplex QuadFormsKB.Tamagawa.Measure.SphereLerayC
open QuadFormsKB.Tamagawa.Measure.OrbitalComplex QuadFormsKB.Tamagawa.Measure.ConeAlgebra
open QuadFormsKB.Tamagawa.Measure.Weil

/-! ### The punctured cone and the action of $SO(Q)$ -/

section ConeType

variable {n : ℕ}

/-- **The punctured cone** $C^\circ = \{z : Q(z) = 0,\ z \ne 0\}$. -/
def coneSet (Q : QuadForm ℂ n) : Set (Fin n → ℂ) := {z | Q.eval z = 0 ∧ z ≠ 0}

/-- $C^\circ$ as a type (Borel structure). -/
abbrev ConeT (Q : QuadForm ℂ n) : Type := ↥(coneSet Q)

theorem measurableSet_coneSet (Q : QuadForm ℂ n) : MeasurableSet (coneSet Q) :=
  ((isClosed_eq (continuous_evalC Q) continuous_const).measurableSet).inter
    (measurableSet_singleton 0).compl

theorem eval_mat_mulVec (Q : QuadForm ℂ n) (g : ArchSOC Q) (z : Fin n → ℂ) :
    Q.eval (ArchSOC.mat Q g *ᵥ z) = Q.eval z :=
  eval_mulVec_of_isometry Q (isometry_hessian_of_gramC (ArchSOC.isometry Q g)) z

theorem mat_mulVec_ne_zero (Q : QuadForm ℂ n) (g : ArchSOC Q) {z : Fin n → ℂ} (hz : z ≠ 0) :
    ArchSOC.mat Q g *ᵥ z ≠ 0 := by
  intro h
  apply hz
  have : ArchSOC.mat Q g⁻¹ *ᵥ (ArchSOC.mat Q g *ᵥ z) = z := by
    rw [mulVec_mulVec, ArchSOC.mat_inv_mul, one_mulVec]
  rw [← this, h, mulVec_zero]

instance (Q : QuadForm ℂ n) : MulAction (ArchSOC Q) (ConeT Q) where
  smul g z := ⟨ArchSOC.mat Q g *ᵥ (z : Fin n → ℂ),
    by rw [eval_mat_mulVec]; exact z.2.1, mat_mulVec_ne_zero Q g z.2.2⟩
  one_smul z := Subtype.ext (by
    show ArchSOC.mat Q 1 *ᵥ (z : Fin n → ℂ) = z
    rw [ArchSOC.mat_one, one_mulVec])
  mul_smul g h z := Subtype.ext (by
    show ArchSOC.mat Q (g * h) *ᵥ (z : Fin n → ℂ) = ArchSOC.mat Q g *ᵥ (ArchSOC.mat Q h *ᵥ z)
    rw [ArchSOC.mat_mul, mulVec_mulVec])

theorem coe_smul_cone (Q : QuadForm ℂ n) (g : ArchSOC Q) (z : ConeT Q) :
    ((g • z : ConeT Q) : Fin n → ℂ) = ArchSOC.mat Q g *ᵥ (z : Fin n → ℂ) := rfl

theorem continuous_smul_cone (Q : QuadForm ℂ n) :
    Continuous fun p : ArchSOC Q × ConeT Q => p.1 • p.2 :=
  ((ArchSOC.continuous_mat Q).comp continuous_fst).matrix_mulVec
    (continuous_subtype_val.comp continuous_snd) |>.subtype_mk _

end ConeType


/-! ### The Leray measure of the cone -/

variable {k : ℕ} {c : ℂ} {Q' : QuadForm ℂ k}

/-- The cone point $q\,(1, y)$. -/
def coneVec (q : ℂ) (y : Fin (k + 1) → ℂ) : Fin (k + 1 + 1) → ℂ := q • (Fin.cons 1 y : Fin (k + 1 + 1) → ℂ)

theorem coneVec_zero (q : ℂ) (y : Fin (k + 1) → ℂ) : coneVec q y 0 = q := by simp [coneVec]

theorem coneVec_succ (q : ℂ) (y : Fin (k + 1) → ℂ) (i : Fin (k + 1)) : coneVec q y i.succ = q * y i := by
  simp [coneVec]

theorem coneVec_mem {q : ℂ} (hq : q ≠ 0) (y : SphC (QmC c Q') (-c)) :
    coneVec q (y : Fin (k + 1) → ℂ) ∈ coneSet (coneForm c Q') := by
  refine ⟨?_, fun h => hq ?_⟩
  · rw [coneVec, eval_smulC, coneForm, eval_splitForm_cons, y.2]; ring
  · have := congrFun h 0; rwa [coneVec_zero] at this

theorem eV_mem (hc : c ≠ 0) : (eV : Fin (k + 1 + 1) → ℂ) ∈ coneSet (coneForm c Q') :=
  ⟨eval_eV c Q', fun h => by have := congrFun h 0; simp [eV] at this⟩

/-- The base point $e = e_0 + e_1 \in C^\circ$. -/
def eCone (hc : c ≠ 0) : ConeT (coneForm c Q') := ⟨eV, eV_mem hc⟩

/-- **The cone chart** $(q, y) \mapsto q\,(1, y)$, $\mathbb R^\times \times S'_{-c} \to C^\circ$ (junk value $e$ at $q = 0$, a
null set). -/
def coneMap (hc : c ≠ 0) (p : ℂ × SphC (QmC c Q') (-c)) : ConeT (coneForm c Q') :=
  if h : p.1 = 0 then eCone hc else ⟨coneVec p.1 (p.2 : Fin (k + 1) → ℂ), coneVec_mem h p.2⟩

theorem coe_coneMap (hc : c ≠ 0) {q : ℂ} (hq : q ≠ 0) (y : SphC (QmC c Q') (-c)) :
    ((coneMap hc (q, y) : ConeT (coneForm c Q')) : Fin (k + 1 + 1) → ℂ) = coneVec q (y : Fin (k + 1) → ℂ) := by
  simp [coneMap, hq]

theorem measurable_coneMap (hc : c ≠ 0) : Measurable (coneMap (Q' := Q') hc) := by
  have hS : MeasurableSet {p : ℂ × SphC (QmC c Q') (-c) | p.1 = 0} :=
    measurable_fst (measurableSet_singleton 0)
  refine measurable_of_restrict_of_restrict_compl hS ?_ ?_
  · have e : {p : ℂ × SphC (QmC c Q') (-c) | p.1 = 0}.domRestrict (coneMap hc) = fun _ => eCone hc := by
      funext p; exact dif_pos p.2
    rw [e]; exact measurable_const
  · have e : {p : ℂ × SphC (QmC c Q') (-c) | p.1 = 0}ᶜ.domRestrict (coneMap hc) = fun p =>
        ⟨coneVec (p : ℂ × SphC (QmC c Q') (-c)).1 ((p : ℂ × SphC (QmC c Q') (-c)).2 : Fin (k + 1) → ℂ),
          coneVec_mem p.2 (p : ℂ × SphC (QmC c Q') (-c)).2⟩ := by
      funext p; exact dif_neg p.2
    rw [e]
    refine Continuous.measurable (Continuous.subtype_mk ?_ _)
    exact ((continuous_fst.comp continuous_subtype_val).smul
      (continuous_const.finCons (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val))))

/-- The radial density $|q|^{k-1}$ (written $|q|^k/|q|$, so that it is $0$ at $q = 0$). -/
def rhoK (k : ℕ) (q : ℂ) : ℝ≥0∞ := (((‖q‖₊ ^ (2 * k)) * (‖q‖₊ ^ 2)⁻¹ : ℝ≥0) : ℝ≥0∞)

theorem measurable_rhoK : Measurable (rhoK k) := by
  unfold rhoK
  exact ((continuous_nnnorm.pow _).measurable.mul (continuous_nnnorm.pow 2).measurable.inv).coe_nnreal_ennreal

/-- **The Leray measure of the punctured cone** $\sigma_C$: the image of $|q|^{k-1}dq \otimes \sigma'_{-c}$ under
$(q, y) \mapsto q(1, y)$ ($\sigma'_{-c}$ = the Leray measure on $S'_{-c}$ for $\langle -c\rangle \perp Q'$). It is
$dx_0 \otimes \sigma'_{-cx_0^2} = dx/dQ$ in the slicing $Q = cx_0^2 + Q_m(x')$ (see the module docstring). -/
@[kb "weil1982" "§2.2 (the Leray form dx/dQ on the cone Q = 0) [unverified]"]
def sigCone (hc : c ≠ 0) : Measure (ConeT (coneForm c Q')) :=
  ((volume.withDensity (rhoK k)).prod (sigC (QmC c Q') (-c))).map (coneMap hc)

theorem lintegral_sigCone (hc : c ≠ 0) {F : ConeT (coneForm c Q') → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z, F z ∂sigCone hc = ∫⁻ q, rhoK k q * ∫⁻ y, F (coneMap hc (q, y)) ∂sigC (QmC c Q') (-c) := by
  have := sigmaFinite_sigC (Q := QmC c Q') (neg_ne_zero.mpr hc) (by omega)
  rw [sigCone, lintegral_map hF (measurable_coneMap hc),
    lintegral_prod (fun p => F (coneMap hc p)) (hF.comp (measurable_coneMap hc)).aemeasurable]
  exact lintegral_withDensity_eq_lintegral_mul _ measurable_rhoK
      (((hF.comp (measurable_coneMap hc)).lintegral_prod_right') :
        Measurable fun q : ℂ => ∫⁻ y, F (coneMap hc (q, y)) ∂sigC (QmC c Q') (-c))



/-! ### An explicit section of $SO(Q) \to C^\circ$ -/

variable (hc : c ≠ 0) (hQ' : gramDetC Q' ≠ 0)

theorem yOf_mem {z : Fin (k + 1 + 1) → ℂ} (hz : z ∈ coneSet (coneForm c Q')) (h0 : z 0 ≠ 0) :
    (fun i : Fin (k + 1) => z i.succ / z 0) ∈ sphC (QmC c Q') (-c) := by
  have hz1 := hz.1
  have e : z = Fin.cons (z 0) (fun i : Fin (k + 1) => z i.succ) := by
    ext i; refine Fin.cases rfl (fun i => rfl) i
  rw [e, coneForm, eval_splitForm_cons] at hz1
  show (QmC c Q').eval _ = -c
  have : (fun i : Fin (k + 1) => z i.succ / z 0) = (z 0)⁻¹ • (fun i : Fin (k + 1) => z i.succ) := by
    ext i; simp [div_eq_inv_mul]
  rw [this, eval_smulC]
  have h2 : (QmC c Q').eval (fun i : Fin (k + 1) => z i.succ) = -c * z 0 ^ 2 := by linear_combination hz1
  rw [h2]; field_simp

/-- The point $y = z'/z_0 \in S'_{-c}$ of $z \in C^\circ$ with $z_0 \ne 0$ ($z = z_0(1, y)$). -/
def yOf {z : ConeT (coneForm c Q')} (h0 : (z : Fin (k + 1 + 1) → ℂ) 0 ≠ 0) : SphC (QmC c Q') (-c) :=
  ⟨fun i => (z : Fin (k + 1 + 1) → ℂ) i.succ / (z : Fin (k + 1 + 1) → ℂ) 0, yOf_mem z.2 h0⟩

theorem coneVec_yOf {z : ConeT (coneForm c Q')} (h0 : (z : Fin (k + 1 + 1) → ℂ) 0 ≠ 0) :
    coneVec ((z : Fin (k + 1 + 1) → ℂ) 0) ((yOf h0 : SphC (QmC c Q') (-c)) : Fin (k + 1) → ℂ) = z := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · rw [coneVec_zero]
  · rw [coneVec_succ]; simp only [yOf]; field_simp

/-- The section on $\{z_0 \ne 0\}$: $s_0(z) = \iota(s'(z'/z_0))\,d(z_0)$. -/
def coneSec₀ (s' : SphSectionC (-c) Q') (z : ConeT (coneForm c Q')) : ArchSOC (coneForm c Q') :=
  if h : (z : Fin (k + 1 + 1) → ℂ) 0 ≠ 0 then iotaC c (QmC c Q') (s'.toFun (yOf h)) * dG hc hQ' h else 1

theorem iota_mulVec_eV (s' : SphSectionC (-c) Q') (y : SphC (QmC c Q') (-c)) :
    ArchSOC.mat _ (iotaC c (QmC c Q') (s'.toFun y)) *ᵥ (eV : Fin (k + 1 + 1) → ℂ) =
      Fin.cons 1 (y : Fin (k + 1) → ℂ) := by
  rw [mat_iotaC, eV, v3, cornerMat_mulVec, one_mul]
  congr 1
  have := s'.spec y
  rw [← this]

theorem coneSec₀_smul (s' : SphSectionC (-c) Q') {z : ConeT (coneForm c Q')}
    (h0 : (z : Fin (k + 1 + 1) → ℂ) 0 ≠ 0) : coneSec₀ hc hQ' s' z • eCone hc = z := by
  apply Subtype.ext
  rw [coe_smul_cone]
  unfold coneSec₀
  rw [dif_pos h0, ArchSOC.mat_mul, mat_dG, ← mulVec_mulVec]
  show _ *ᵥ (dM _ *ᵥ (eV : Fin (k + 1 + 1) → ℂ)) = _
  rw [dM_mulVec_eV h0, mulVec_smul, iota_mulVec_eV]
  conv_rhs => rw [← coneVec_yOf h0]
  rfl


theorem measurable_coneSec₀ (s' : SphSectionC (-c) Q') : Measurable (coneSec₀ hc hQ' s') := by
  set U : Set (ConeT (coneForm c Q')) := {z | (z : Fin (k + 1 + 1) → ℂ) 0 ≠ 0}
  have hU : MeasurableSet U :=
    (isOpen_ne_fun ((continuous_apply 0).comp continuous_subtype_val) continuous_const).measurableSet
  refine measurable_of_restrict_of_restrict_compl hU ?_ ?_
  · have e : U.domRestrict (coneSec₀ hc hQ' s') = fun z : ↥U =>
        iotaC c (QmC c Q') (s'.toFun (yOf (z := z.1) z.2)) * dG hc hQ' (show (z.1 : Fin (k + 1 + 1) → ℂ) 0 ≠ 0 from z.2) := by
      funext z; show coneSec₀ hc hQ' s' z.1 = _; unfold coneSec₀
      rw [dif_pos (show ((z : ConeT (coneForm c Q')) : Fin (k + 1 + 1) → ℂ) 0 ≠ 0 from z.2)]
    rw [e]
    have hz0 : Continuous fun z : ↥U => ((z : ConeT (coneForm c Q')) : Fin (k + 1 + 1) → ℂ) 0 :=
      (continuous_apply 0).comp (continuous_subtype_val.comp continuous_subtype_val)
    have hy0 : Continuous fun z : ↥U => (⟨fun i : Fin (k + 1) =>
        ((z : ConeT (coneForm c Q')) : Fin (k + 1 + 1) → ℂ) i.succ /
          ((z : ConeT (coneForm c Q')) : Fin (k + 1 + 1) → ℂ) 0,
        yOf_mem (z : ConeT (coneForm c Q')).2 z.2⟩ : SphC (QmC c Q') (-c)) := by
      refine Continuous.subtype_mk (continuous_pi fun i => ?_) _
      exact ((continuous_apply i.succ).comp (continuous_subtype_val.comp continuous_subtype_val)).div hz0
        (fun z => z.2)
    have hy : Continuous fun z : ↥U => (yOf (z := z.1) z.2 : SphC (QmC c Q') (-c)) := hy0
    have h1 : Measurable fun z : ↥U => iotaC c (QmC c Q') (s'.toFun (yOf (z := z.1) z.2)) := by
      have := (continuous_iotaC c (QmC c Q')).measurable.comp (s'.measurable.comp hy.measurable)
      simp only [Function.comp_def] at this
      exact this
    have h2 : Continuous fun z : ↥U =>
        dG hc hQ' (show ((z : ConeT (coneForm c Q')) : Fin (k + 1 + 1) → ℂ) 0 ≠ 0 from z.2) := by
      have hf : Continuous fun z : ↥U => (⟨((z : ConeT (coneForm c Q')) : Fin (k + 1 + 1) → ℂ) 0, z.2⟩ :
        {a : ℂ // a ≠ 0}) := hz0.subtype_mk _
      have := (continuous_dG' hc hQ').comp hf
      simp only [Function.comp_def] at this
      exact this
    exact h1.mul h2.measurable
  · have e : Uᶜ.domRestrict (coneSec₀ hc hQ' s') = fun _ => 1 := by
      funext z; show coneSec₀ hc hQ' s' z.1 = _; unfold coneSec₀
      rw [dif_neg (show ¬ (((z : ConeT (coneForm c Q')) : Fin (k + 1 + 1) → ℂ) 0 ≠ 0) from z.2)]
    rw [e]; exact measurable_const

/-- The finite list $1,\ d(2),\ n(\varepsilon_1), \dots, n(\varepsilon_k)$: every $z \in C^\circ$ is moved into
$\{z_0 \ne 0\}$ by one of them. -/
def coneList : List (ArchSOC (coneForm c Q')) :=
  1 :: dG hc hQ' (two_ne_zero) :: List.ofFn (fun j : Fin k => nG hc hQ' (Pi.single j 1))

theorem cone_cover (z : ConeT (coneForm c Q')) :
    ∃ g ∈ coneList hc hQ', ((g • z : ConeT (coneForm c Q')) : Fin (k + 1 + 1) → ℂ) 0 ≠ 0 := by
  obtain ⟨x, hx⟩ := z
  by_cases h0 : x 0 ≠ 0
  · exact ⟨1, List.mem_cons_self .., by rw [one_smul]; exact h0⟩
  push Not at h0
  by_cases h1 : x 1 ≠ 0
  · refine ⟨dG hc hQ' two_ne_zero, List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_⟩
    rw [coe_smul_cone, mat_dG]
    show (dM 2 *ᵥ x) 0 ≠ 0
    rw [← v3_eta x, dM_mulVec_v3, v3_zero', h0]
    intro h; apply h1; linear_combination (4 / 3 : ℂ) * h
  push Not at h1
  have hy : tl x ≠ 0 := by
    intro hy; apply hx.2
    rw [← v3_eta x, h0, h1, hy]
    ext i; refine Fin.cases rfl (fun i => Fin.cases rfl (fun i => rfl) i) i
  have hHy : Q'.hessian *ᵥ tl x ≠ 0 := fun h => hy (Matrix.eq_zero_of_mulVec_eq_zero (hessian_det_ne_zeroC hQ') h)
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hHy
  refine ⟨nG hc hQ' (Pi.single j 1), List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_ofFn.mpr ⟨j, rfl⟩)), ?_⟩
  rw [coe_smul_cone, mat_nG]
  show (nM c Q' (Pi.single j 1) *ᵥ x) 0 ≠ 0
  rw [← v3_eta x, nM_mulVec_v3, v3_zero', h0, h1, hess_dot_comm, dotProduct_single,
    mul_one]
  simp only [sub_zero, zero_mul, add_zero, zero_sub, neg_ne_zero]
  exact div_ne_zero hj (mul_ne_zero two_ne_zero hc)

omit hc hQ' in
theorem measurable_smul_cone (g : ArchSOC (coneForm c Q')) :
    Measurable fun z : ConeT (coneForm c Q') => g • z :=
  ((continuous_smul_cone _).comp (continuous_const.prodMk continuous_id)).measurable

/-- **An explicit measurable section** of $g \mapsto ge$, $SO(Q)(\mathbb R) \to C^\circ$, as `OrbitSection`:
$s(z) = \iota(s'(z'/z_0))\,d(z_0)$ when $z_0 \ne 0$, else $g^{-1}s(gz)$ for the first $g \in \{d(2), n(\varepsilon_j)\}$
with $(gz)_0 \ne 0$. (In particular $SO(Q)(\mathbb R)$ is transitive on $C^\circ$.) -/
abbrev coneOrbitSection (s' : SphSectionC (-c) Q') : OrbitSection (ArchSOC (coneForm c Q')) (ConeT (coneForm c Q')) where
  base := eCone hc
  sec := ConeReal.extSec {z | (z : Fin (k + 1 + 1) → ℂ) 0 ≠ 0} (coneSec₀ hc hQ' s') (coneList hc hQ')
  sec_smul z := ConeReal.extSec_smul (fun z hz => coneSec₀_smul hc hQ' s' hz) _ (cone_cover hc hQ' z)
  measurable_sec := ConeReal.measurable_extSec
    (isOpen_ne_fun ((continuous_apply 0).comp continuous_subtype_val) continuous_const).measurableSet
    (measurable_coneSec₀ hc hQ' s') measurable_smul_cone _
  measurable_orbit := ((continuous_smul_cone _).comp (continuous_id.prodMk continuous_const)).measurable

theorem coneOrbitSection_sec_of_ne (s' : SphSectionC (-c) Q') {z : ConeT (coneForm c Q')}
    (h0 : (z : Fin (k + 1 + 1) → ℂ) 0 ≠ 0) :
    (coneOrbitSection hc hQ' s').sec z = iotaC c (QmC c Q') (s'.toFun (yOf h0)) * dG hc hQ' h0 := by
  have e : (coneOrbitSection hc hQ' s').sec z = ConeReal.extSec {z : ConeT (coneForm c Q') |
      (z : Fin (k + 1 + 1) → ℂ) 0 ≠ 0} (coneSec₀ hc hQ' s') (1 :: (dG hc hQ' two_ne_zero ::
        List.ofFn (fun j : Fin k => nG hc hQ' (Pi.single j 1)))) z := rfl
  rw [e, ConeReal.extSec_cons_of_mem _ (show z ∈ {z : ConeT (coneForm c Q') | (z : Fin (k + 1 + 1) → ℂ) 0 ≠ 0} from h0)]
  unfold coneSec₀; rw [dif_pos h0]


/-! ### The stabilizer $P$ of $e$ and its Haar measure -/

omit hQ' in
/-- The stabilizer $P = \mathrm{Stab}(e)$ in $SO(Q)(\mathbb R)$. -/
abbrev stabP : Subgroup (ArchSOC (coneForm c Q')) := MulAction.stabilizer (ArchSOC (coneForm c Q')) (eCone (Q' := Q') hc)

theorem nG_mG_mem (w : Fin k → ℂ) (h : ArchSOC Q') : nG hc hQ' w * mG c Q' h ∈ stabP (Q' := Q') hc := by
  rw [MulAction.mem_stabilizer_iff]
  apply Subtype.ext
  rw [coe_smul_cone, ArchSOC.mat_mul, mat_nG, mat_mG, ← mulVec_mulVec]
  show nM c Q' w *ᵥ (mM _ *ᵥ (eV : Fin (k + 1 + 1) → ℂ)) = eV
  rw [mM_mulVec_eV, nM_mulVec_eV]

/-- The parametrization $(w, h) \mapsto n(w)\,\mathrm{diag}(1, 1, h)$ of $P = N \rtimes SO(Q')$. -/
def pElem (p : (Fin k → ℂ) × ArchSOC Q') : stabP (Q' := Q') hc := ⟨nG hc hQ' p.1 * mG c Q' p.2, nG_mG_mem hc hQ' p.1 p.2⟩

theorem continuous_pElem : Continuous (pElem (Q' := Q') hc hQ') :=
  (((continuous_nG hc hQ').comp continuous_fst).mul (continuous_mG.comp continuous_snd)).subtype_mk _

/-- **The Haar measure of $P$**: $\mu_P = (w, h) \mapsto n(w)\mathrm{diag}(1,1,h)$ applied to $dw \otimes \mu_{Q'}$
(Lebesgue measure on $V' = \mathbb R^k$ in the coordinates of `nG`, times the Leray measure of $SO(Q')$). -/
def muP : Measure (stabP (Q' := Q') hc) := (volume.prod (lerayMeasureC Q' hQ')).map (pElem hc hQ')

theorem lintegral_muP {f : stabP (Q' := Q') hc → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ p, f p ∂muP hc hQ' = ∫⁻ w, ∫⁻ h, f (pElem hc hQ' (w, h)) ∂lerayMeasureC Q' hQ' := by
  have := isHaarMeasure_lerayMeasureC hQ'
  rw [muP, lintegral_map hf (continuous_pElem hc hQ').measurable,
    lintegral_prod (fun p => f (pElem hc hQ' p)) (hf.comp (continuous_pElem hc hQ').measurable).aemeasurable]

/-! ### The cone orbital identity -/

theorem yOf_coneMap {q : ℂ} (hq : q ≠ 0) (y : SphC (QmC c Q') (-c))
    (h0 : ((coneMap hc (q, y) : ConeT (coneForm c Q')) : Fin (k + 1 + 1) → ℂ) 0 ≠ 0) : yOf h0 = y := by
  apply Subtype.ext
  funext i
  show ((coneMap hc (q, y) : ConeT (coneForm c Q')) : Fin (k + 1 + 1) → ℂ) i.succ /
    ((coneMap hc (q, y) : ConeT (coneForm c Q')) : Fin (k + 1 + 1) → ℂ) 0 = _
  rw [coe_coneMap hc hq, coneVec_succ, coneVec_zero]; field_simp

theorem coneMap_zero_ne {q : ℂ} (hq : q ≠ 0) (y : SphC (QmC c Q') (-c)) :
    ((coneMap hc (q, y) : ConeT (coneForm c Q')) : Fin (k + 1 + 1) → ℂ) 0 ≠ 0 := by
  rw [coe_coneMap hc hq, coneVec_zero]; exact hq

theorem sec_coneMap (s' : SphSectionC (-c) Q') {q : ℂ} (hq : q ≠ 0) (y : SphC (QmC c Q') (-c)) :
    (coneOrbitSection hc hQ' s').sec (coneMap hc (q, y)) = iotaC c (QmC c Q') (s'.toFun y) * dGt hc hQ' q := by
  rw [coneOrbitSection_sec_of_ne hc hQ' s' (coneMap_zero_ne hc hq y), yOf_coneMap hc hq y, dGt_of_ne hc hQ' hq]
  congr 1
  exact mat_ext' (by rw [mat_dG, mat_dG, coe_coneMap hc hq, coneVec_zero])

instance : SFinite (muP hc hQ') := by
  have := isHaarMeasure_lerayMeasureC hQ'
  unfold muP; infer_instance

/-- **The cone orbital identity at a complex place** ($Q = \langle c\rangle\perp\langle -c\rangle\perp Q'$ over
$\mathbb C$, $Q'$ nondegenerate in $k \ge 1$ variables, $c \ne 0$):
$$\mu_Q = |2c|_{\mathbb C}^{-2(k+1)}\cdot\Psi_*(\sigma_C \otimes \mu_P),\qquad |z|_{\mathbb C} = |z|^2,$$
with $\mu_Q$ the Leray measure, $\sigma_C$ the complex cone measure (`sigCone`), $\mu_P$ the Haar measure
$d^2w\otimes\mu_{Q'}$ of $P = N \rtimes SO(Q')$, and $\Psi(z, p) = s(z)p$ for the explicit section `coneOrbitSection`. -/
@[kb "weil1982" "§2.4 (Lemma 2.4.1 / Theorem 2.4.3 for the cone orbit, complex place) [unverified]"]
theorem lerayMeasureC_cone_orbital (s' : SphSectionC (-c) Q') :
    lerayMeasureC (coneForm c Q') (gramDetC_cone hc hQ') =
      (((‖2 * c‖₊ ^ (2 * (2 * k + 2)))⁻¹ : ℝ≥0) : ℝ≥0∞) •
        (coneOrbitSection hc hQ' s').fibMeasure (sigCone hc) (muP hc hQ') := by
  have := isHaarMeasure_lerayMeasureC hQ'
  have := sigmaFinite_sigC (Q := QmC c Q') (neg_ne_zero.mpr hc) (by omega)
  have key : ∀ f : ArchSOC (coneForm c Q') → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂lerayMeasureC (coneForm c Q') (gramDetC_cone hc hQ') =
        (((‖2 * c‖₊ ^ (2 * (2 * k + 2)))⁻¹ : ℝ≥0) : ℝ≥0∞) *
          ∫⁻ g, f g ∂(coneOrbitSection hc hQ' s').fibMeasure (sigCone hc) (muP hc hQ') := by
    intro f hf
    set S := coneOrbitSection hc hQ' s'
    have hsec : Measurable fun p : ConeT (coneForm c Q') × stabP (Q' := Q') hc => f (S.sec p.1 * p.2) :=
      hf.comp ((S.measurable_sec.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd))
    rw [S.lintegral_fibMeasure _ _ hf, lintegral_sigCone hc hsec.lintegral_prod_right',
      lintegral_lerayMeasureC_cone_param hc hQ' s' hf]
    have hae : ∀ᵐ q : ℂ, q ≠ 0 := by
      rw [ae_iff]; simp only [ne_eq, not_not, ofPred_eq_eq_singleton, measure_singleton]
    have hc2 : ‖2 * c‖₊ ≠ 0 := nnnorm_ne_zero_iff.mpr (mul_ne_zero two_ne_zero hc)
    have hK : (((‖2 * c‖₊ ^ (2 * (2 * k + 2)))⁻¹ : ℝ≥0) : ℝ≥0∞) =
        (((‖2 * c‖₊ ^ (2 * (k + 1)))⁻¹ : ℝ≥0) : ℝ≥0∞) * (((‖2 * c‖₊ ^ (2 * k))⁻¹ : ℝ≥0) : ℝ≥0∞) *
          (((‖2 * c‖₊ ^ 2)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
      rw [← ENNReal.coe_mul, ← ENNReal.coe_mul, ← mul_inv, ← mul_inv, ← pow_add, ← pow_add]
      congr 3; ring
    rw [hK, mul_assoc _ (((‖2 * c‖₊ ^ 2)⁻¹ : ℝ≥0) : ℝ≥0∞), ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    congr 1
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with q hq
    have hdens : dens2 (2 * c) q * ((‖q‖₊ ^ (2 * k) : ℝ≥0) : ℝ≥0∞) =
        (((‖2 * c‖₊ ^ 2)⁻¹ : ℝ≥0) : ℝ≥0∞) * rhoK k q := by
      unfold dens2 rhoK
      rw [← ENNReal.coe_mul, ← ENNReal.coe_mul, nnnorm_mul, mul_pow, mul_inv]
      congr 1; ring
    rw [hdens, mul_assoc]
    congr 1
    refine congrArg _ ?_
    refine lintegral_congr fun y => ?_
    have hm2 : Measurable fun p : ArchSOC Q' × (Fin k → ℂ) =>
        f (iotaC c (QmC c Q') (s'.toFun y) * dGt hc hQ' q * nG hc hQ' p.2 * mG c Q' p.1) :=
      hf.comp ((measurable_const.mul ((continuous_nG hc hQ').measurable.comp measurable_snd)).mul
        (continuous_mG.measurable.comp measurable_fst))
    have hmP : Measurable fun p : stabP (Q' := Q') hc => f (S.sec (coneMap hc (q, y)) * (p : ArchSOC _)) :=
      hf.comp (measurable_const.mul measurable_subtype_coe)
    rw [lintegral_muP hc hQ' hmP, lintegral_lintegral_swap hm2.aemeasurable]
    show _ = ∫⁻ w, ∫⁻ h, f ((coneOrbitSection hc hQ' s').sec (coneMap hc (q, y)) *
      (nG hc hQ' w * mG c Q' h)) ∂lerayMeasureC Q' hQ'
    rw [sec_coneMap hc hQ' s' hq]
    refine lintegral_congr fun w => lintegral_congr fun h => ?_
    simp only [mul_assoc]
  ext A hA
  rw [Measure.smul_apply, ← lintegral_indicator_one hA, ← lintegral_indicator_one hA,
    key _ (measurable_one.indicator hA), smul_eq_mul]

/-! ### $P$ is the full stabilizer; $\mu_P$ is a bi-invariant Haar measure -/

theorem mG_mulVec_e₀ (h : ArchSOC Q') :
    ArchSOC.mat _ (mG c Q' h) *ᵥ (e₀ : Fin (k + 1 + 1) → ℂ) = e₀ := by
  rw [mat_mG, e₀_eq_v3, mM_mulVec_v3, mulVec_zero]

theorem pElem_injective : Function.Injective (pElem (Q' := Q') hc hQ') := by
  rintro ⟨w, h⟩ ⟨w', h'⟩ he
  have he' : nG hc hQ' w * mG c Q' h = nG hc hQ' w' * mG c Q' h' := congrArg Subtype.val he
  have hw : w = w' := by
    have := congrArg (fun g => tl (ArchSOC.mat _ g *ᵥ (e₀ : Fin (k + 1 + 1) → ℂ))) he'
    simp only [ArchSOC.mat_mul, ← mulVec_mulVec, mG_mulVec_e₀, mat_nG, nM_mulVec_e₀ c Q' hc, tl_v3] at this
    exact this
  subst hw
  rw [mul_right_inj] at he'
  have hi : Function.Injective (mG c Q') := by
    intro a b hab
    have := congrArg (ArchSOC.mat _) hab
    rw [mat_mG, mat_mG, mM, mM] at this
    apply Subtype.ext; apply Units.ext
    exact cornerMat_injective_right (cornerMat_injective_right this)
  rw [hi he']

/-- **$P = \mathrm{Stab}(e) = N \rtimes SO(Q')$**: every $g \in SO(Q)(\mathbb R)$ fixing $e$ is $n(w)\,\mathrm{diag}(1,1,h)$. -/
theorem exists_pElem (g : stabP (Q' := Q') hc) : ∃ p, pElem hc hQ' p = g := by
  have hg := (MulAction.mem_stabilizer_iff.mp g.2)
  have he : ArchSOC.mat _ (g : ArchSOC (coneForm c Q')) *ᵥ (eV : Fin (k + 1 + 1) → ℂ) = eV :=
    congrArg Subtype.val hg
  have hiso : (ArchSOC.mat _ (g : ArchSOC (coneForm c Q')))ᵀ * (coneForm c Q').hessian *
      ArchSOC.mat _ (g : ArchSOC (coneForm c Q')) = (coneForm c Q').hessian :=
    isometry_hessian_of_gramC (ArchSOC.isometry _ _)
  obtain ⟨M, hM, hgM⟩ := eq_nM_mul_mM_of_fix c Q' hc _ hiso he
  have hdet : M.det = 1 := by
    have := ArchSOC.det_mat _ (g : ArchSOC (coneForm c Q'))
    rwa [hgM, det_mul, det_nM c Q' hc (hessian_cone_detC hc hQ'), one_mul, det_mM] at this
  have hu : IsUnit M.det := by rw [hdet]; exact isUnit_one
  let u : GL (Fin k) ℂ := ⟨M, M⁻¹, Matrix.mul_nonsing_inv M hu, Matrix.nonsing_inv_mul M hu⟩
  have hmem : u ∈ soC Q' := (mem_soC_iff _ _).mpr ⟨isometry_gramC_of_hessian hM, hdet⟩
  refine ⟨(tl (ArchSOC.mat _ (g : ArchSOC (coneForm c Q')) *ᵥ e₀), ArchSOC.mk _ u hmem), ?_⟩
  apply Subtype.ext
  refine mat_ext' ?_
  show ArchSOC.mat _ (nG hc hQ' _ * mG c Q' (ArchSOC.mk Q' u hmem)) = _
  rw [ArchSOC.mat_mul, mat_nG, mat_mG, ArchSOC.mat_mk]; exact hgM.symm

theorem measurableEmbedding_pElem : MeasurableEmbedding (pElem (Q' := Q') hc hQ') :=
  (continuous_pElem hc hQ').measurableEmbedding (pElem_injective hc hQ')

instance : SigmaFinite (muP hc hQ') := by
  have := isHaarMeasure_lerayMeasureC hQ'
  exact (measurableEmbedding_pElem hc hQ').sigmaFinite_map

theorem muP_ne_zero : muP hc hQ' ≠ 0 := by
  have := isHaarMeasure_lerayMeasureC hQ'
  intro h
  have := congrArg (fun μ => μ univ) h
  simp only [muP] at this
  rw [Measure.map_apply (continuous_pElem hc hQ').measurable MeasurableSet.univ, preimage_univ,
    ← univ_prod_univ, Measure.prod_prod, Measure.coe_zero, Pi.zero_apply] at this
  rcases mul_eq_zero.mp this with h1 | h1
  · exact NeZero.ne _ (Measure.measure_univ_eq_zero.mp h1)
  · exact NeZero.ne _ (Measure.measure_univ_eq_zero.mp h1)

theorem pElem_mul (w w' : Fin k → ℂ) (h h' : ArchSOC Q') :
    (pElem hc hQ' (w, h) : ArchSOC (coneForm c Q')) * pElem hc hQ' (w', h') =
      pElem hc hQ' (w + ArchSOC.mat _ h *ᵥ w', h * h') := by
  show nG hc hQ' w * mG c Q' h * (nG hc hQ' w' * mG c Q' h') =
    nG hc hQ' (w + ArchSOC.mat _ h *ᵥ w') * mG c Q' (h * h')
  rw [map_mul, ← nG_add, mul_assoc, ← mul_assoc (mG c Q' h), mG_mul_nG]
  simp only [mul_assoc]

/-- **$\mu_P$ is left invariant** (a left Haar measure of $P$). -/
instance isMulLeftInvariant_muP : (muP hc hQ').IsMulLeftInvariant := by
  have := isHaarMeasure_lerayMeasureC hQ'
  refine ⟨fun p₀ => ?_⟩
  obtain ⟨⟨w₀, h₀⟩, rfl⟩ := exists_pElem hc hQ' p₀
  have hT : MeasurePreserving (fun p : (Fin k → ℂ) × ArchSOC Q' => (w₀ + ArchSOC.mat _ h₀ *ᵥ p.1, h₀ * p.2))
      (volume.prod (lerayMeasureC Q' hQ')) (volume.prod (lerayMeasureC Q' hQ')) := by
    have h1 : MeasurePreserving (fun w : Fin k → ℂ => w₀ + ArchSOC.mat _ h₀ *ᵥ w) volume volume :=
      (measurePreserving_add_left volume w₀).comp
        (measurePreserving_mulVecC _ (by rw [ArchSOC.det_mat, norm_one]))
    have h2 : MeasurePreserving (fun h : ArchSOC Q' => h₀ * h) (lerayMeasureC Q' hQ') (lerayMeasureC Q' hQ') :=
      measurePreserving_mul_left _ h₀
    exact h1.prod h2
  have e : (fun p : stabP (Q' := Q') hc => pElem hc hQ' (w₀, h₀) * p) ∘ pElem hc hQ' =
      pElem hc hQ' ∘ fun p : (Fin k → ℂ) × ArchSOC Q' => (w₀ + ArchSOC.mat _ h₀ *ᵥ p.1, h₀ * p.2) := by
    funext p; apply Subtype.ext; exact pElem_mul hc hQ' w₀ p.1 h₀ p.2
  rw [muP, Measure.map_map (measurable_const_mul _) (continuous_pElem hc hQ').measurable, e,
    ← Measure.map_map (continuous_pElem hc hQ').measurable hT.measurable, hT.map_eq]

/-- **$\mu_P$ is right invariant**: $P = N \rtimes SO(Q')$ is unimodular (the modular character is trivial), so
$\mu_P$ is the Haar measure of $P$ on both sides and $G/P = C^\circ$ carries the invariant measure $\sigma_C$. -/
instance isMulRightInvariant_muP : (muP hc hQ').IsMulRightInvariant := by
  have := isHaarMeasure_lerayMeasureC hQ'
  have := isMulRightInvariant_lerayMeasureC hQ'
  refine ⟨fun p₀ => ?_⟩
  obtain ⟨⟨w₀, h₀⟩, rfl⟩ := exists_pElem hc hQ' p₀
  have key : ∀ F : stabP (Q' := Q') hc → ℝ≥0∞, Measurable F →
      ∫⁻ p, F (p * pElem hc hQ' (w₀, h₀)) ∂muP hc hQ' = ∫⁻ p, F p ∂muP hc hQ' := by
    intro F hF
    have hF' : Measurable fun p : stabP (Q' := Q') hc => F (p * pElem hc hQ' (w₀, h₀)) :=
      hF.comp (measurable_mul_const _)
    have hm : Measurable fun p : (Fin k → ℂ) × ArchSOC Q' => F (pElem hc hQ' p * pElem hc hQ' (w₀, h₀)) :=
      hF'.comp (continuous_pElem hc hQ').measurable
    have hm' : Measurable fun p : (Fin k → ℂ) × ArchSOC Q' => F (pElem hc hQ' p) :=
      hF.comp (continuous_pElem hc hQ').measurable
    rw [lintegral_muP hc hQ' hF', lintegral_muP hc hQ' hF,
      lintegral_lintegral_swap hm.aemeasurable]
    conv_rhs => rw [lintegral_lintegral_swap hm'.aemeasurable]
    have e1 : ∀ h : ArchSOC Q', ∫⁻ w, F (pElem hc hQ' (w, h) * pElem hc hQ' (w₀, h₀)) =
        ∫⁻ w, F (pElem hc hQ' (w, h * h₀)) := by
      intro h
      have e : ∀ w, pElem hc hQ' (w, h) * pElem hc hQ' (w₀, h₀) =
          pElem hc hQ' (w + ArchSOC.mat _ h *ᵥ w₀, h * h₀) := by
        intro w; apply Subtype.ext; exact pElem_mul hc hQ' w w₀ h h₀
      simp_rw [e]
      exact lintegral_add_right_eq_self (fun w => F (pElem hc hQ' (w, h * h₀))) _
    simp_rw [e1]
    exact lintegral_mul_right_eq_self (fun h => ∫⁻ w, F (pElem hc hQ' (w, h))) h₀
  ext A hA
  rw [Measure.map_apply (measurable_mul_const _) hA, ← lintegral_indicator_one (measurable_mul_const _ hA),
    ← lintegral_indicator_one hA, ← key _ (measurable_one.indicator hA)]
  refine lintegral_congr fun a => ?_
  rfl


/-! ### Invariance and homogeneity of $\sigma_C$ -/

instance : SFinite (sigCone (Q' := Q') hc) := by
  have := sigmaFinite_sigC (Q := QmC c Q') (neg_ne_zero.mpr hc) (by omega)
  unfold sigCone; infer_instance

include hQ' in
/-- **$\sigma_C$ is $SO(Q)(\mathbb C)$-invariant** ($k \ge 1$): from the cone orbital identity, the left invariance of
$\mu_Q$ and of $\mu_P$, and the uniqueness of the quotient measure (`fibMeasure_injective`). -/
@[kb "weil1982" "§2.4 (the invariant measure on G/H) [unverified]"]
theorem map_smul_sigCone (hk : 1 ≤ k) (g : ArchSOC (coneForm c Q')) :
    (sigCone (Q' := Q') hc).map (fun z => g • z) = sigCone hc := by
  set s' : SphSectionC (-c) Q' := sphSectionC (neg_ne_zero.mpr hc) hk hQ'
  set S := coneOrbitSection hc hQ' s'
  have := isHaarMeasure_lerayMeasureC (gramDetC_cone hc hQ')
  have h1 := lerayMeasureC_cone_orbital hc hQ' s'
  have h2 : (lerayMeasureC (coneForm c Q') (gramDetC_cone hc hQ')).map (g * ·) =
      lerayMeasureC (coneForm c Q') (gramDetC_cone hc hQ') := map_mul_left_eq_self _ g
  rw [h1, Measure.map_smul _ (measurable_const_mul g).aemeasurable, ConeReal.fibMeasure_map_mul_left S] at h2
  set K := (((‖2 * c‖₊ ^ (2 * (2 * k + 2)))⁻¹ : ℝ≥0) : ℝ≥0∞)
  have hK0 : K ≠ 0 := by
    simp only [K, ne_eq, ENNReal.coe_eq_zero, inv_eq_zero, pow_eq_zero_iff', nnnorm_eq_zero, not_and, not_not]
    intro h; exact absurd h (mul_ne_zero two_ne_zero hc)
  have hKt : K ≠ ⊤ := ENNReal.coe_ne_top
  have h3 : S.fibMeasure ((sigCone hc).map fun z => g • z) (muP hc hQ') = S.fibMeasure (sigCone hc) (muP hc hQ') := by
    have := congrArg (fun μ => K⁻¹ • μ) h2
    simp only [smul_smul, ENNReal.inv_mul_cancel hK0 hKt, one_smul] at this
    exact this
  exact S.fibMeasure_injective (muP hc hQ') (muP_ne_zero hc hQ') h3

include hQ' in
theorem smulInvariantMeasure_sigCone (hk : 1 ≤ k) :
    SMulInvariantMeasure (ArchSOC (coneForm c Q')) (ConeT (coneForm c Q')) (sigCone (Q' := Q') hc) := by
  refine ⟨fun g A hA => ?_⟩
  have := congrArg (fun μ => μ A) (map_smul_sigCone hc hQ' hk g)
  rwa [Measure.map_apply (measurable_smul_cone g) hA] at this

omit hQ' in
theorem smul_mem_coneSet {a : ℂ} (ha : a ≠ 0) {z : Fin (k + 1 + 1) → ℂ} (hz : z ∈ coneSet (coneForm c Q')) :
    a • z ∈ coneSet (coneForm c Q') :=
  ⟨by rw [eval_smulC, hz.1, mul_zero], smul_ne_zero ha hz.2⟩

omit hQ' in
/-- Scaling $z \mapsto az$ on the cone. -/
def coneScale {a : ℂ} (ha : a ≠ 0) (z : ConeT (coneForm c Q')) : ConeT (coneForm c Q') :=
  ⟨a • (z : Fin (k + 1 + 1) → ℂ), smul_mem_coneSet ha z.2⟩

omit hQ' in
theorem measurable_coneScale {a : ℂ} (ha : a ≠ 0) : Measurable (coneScale (Q' := Q') (c := c) ha) :=
  (((continuous_const_smul a).comp continuous_subtype_val).subtype_mk
    (fun z : ConeT (coneForm c Q') => smul_mem_coneSet ha z.2)).measurable

omit hQ' in
/-- **Homogeneity** (complex): $(z \mapsto az)_*\sigma_C = |a|_{\mathbb C}^{-k}\sigma_C$, i.e.
$\sigma_C(aA) = |a|^{2k}\sigma_C(A)$. -/
@[kb "weil1982" "§2.2 (homogeneity of the Leray form on the cone) [unverified]"]
theorem map_coneScale_sigCone {a : ℂ} (ha : a ≠ 0) :
    (sigCone (Q' := Q') hc).map (coneScale ha) = ((‖a⁻¹‖₊ ^ (2 * k) : ℝ≥0) : ℝ≥0∞) • sigCone hc := by
  have := sigmaFinite_sigC (Q := QmC c Q') (neg_ne_zero.mpr hc) (by omega)
  ext A hA
  have hF : Measurable (A.indicator (1 : ConeT (coneForm c Q') → ℝ≥0∞)) := measurable_one.indicator hA
  rw [Measure.map_apply (measurable_coneScale ha) hA, Measure.smul_apply, smul_eq_mul,
    ← lintegral_indicator_one (measurable_coneScale ha hA), ← lintegral_indicator_one hA]
  rw [show (∫⁻ z, (coneScale ha ⁻¹' A).indicator 1 z ∂sigCone (Q' := Q') hc) =
      ∫⁻ z, A.indicator (1 : ConeT (coneForm c Q') → ℝ≥0∞) (coneScale ha z) ∂sigCone hc from rfl,
    lintegral_sigCone hc (F := fun z => A.indicator (1 : ConeT (coneForm c Q') → ℝ≥0∞) (coneScale ha z))
      (hF.comp (measurable_coneScale ha)), lintegral_sigCone hc hF]
  set G : ℂ → ℝ≥0∞ := fun u => ∫⁻ y, A.indicator 1 (coneMap hc (u, y)) ∂sigC (QmC c Q') (-c) with hG
  have hGm : Measurable G := (hF.comp (measurable_coneMap hc)).lintegral_prod_right'
  have hae : ∀ᵐ q : ℂ, q ≠ 0 := by
    rw [ae_iff]; simp only [ne_eq, not_not, ofPred_eq_eq_singleton, measure_singleton]
  have ha0 : ‖a‖₊ ≠ 0 := nnnorm_ne_zero_iff.mpr ha
  have h1 : ∫⁻ q, rhoK k q * ∫⁻ y, A.indicator (1 : ConeT (coneForm c Q') → ℝ≥0∞)
      (coneScale ha (coneMap hc (q, y))) ∂sigC (QmC c Q') (-c) =
      ∫⁻ q, ((‖a⁻¹‖₊ ^ (2 * k) : ℝ≥0) : ℝ≥0∞) * ((‖a‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) * (rhoK k (a * q) * G (a * q)) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with q hq
    have e : ∀ y : SphC (QmC c Q') (-c), A.indicator (1 : ConeT (coneForm c Q') → ℝ≥0∞)
        (coneScale ha (coneMap hc (q, y))) = A.indicator 1 (coneMap hc (a * q, y)) := by
      intro y
      have : coneScale ha (coneMap hc (q, y)) = coneMap hc (a * q, y) := by
        apply Subtype.ext
        show a • ((coneMap hc (q, y) : ConeT (coneForm c Q')) : Fin (k + 1 + 1) → ℂ) = _
        rw [coe_coneMap hc hq, coe_coneMap hc (mul_ne_zero ha hq), coneVec, coneVec, smul_smul]
      rw [this]
    simp_rw [e]
    have hq0 : ‖q‖₊ ≠ 0 := nnnorm_ne_zero_iff.mpr hq
    have hr : rhoK k q = ((‖a⁻¹‖₊ ^ (2 * k) : ℝ≥0) : ℝ≥0∞) * ((‖a‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) * rhoK k (a * q) := by
      unfold rhoK
      rw [← ENNReal.coe_mul, ← ENNReal.coe_mul]
      congr 1
      rw [nnnorm_mul, nnnorm_inv, mul_pow, mul_pow, inv_pow]
      field_simp
    rw [hr, mul_assoc]
  have haff := lintegral_comp_affineC (Ψ := fun u => rhoK k u * G u) (measurable_rhoK.mul hGm) ha 0
  simp only [add_zero] at haff
  rw [h1, lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top), haff]
  rw [mul_assoc, ← mul_assoc ((‖a‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞), ← ENNReal.coe_mul,
    mul_inv_cancel₀ (pow_ne_zero _ ha0), ENNReal.coe_one, one_mul]

end QuadFormsKB.Tamagawa.Measure.ConeComplex
