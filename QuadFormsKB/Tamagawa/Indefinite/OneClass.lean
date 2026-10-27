/-
# One proper class in the genus: Eichler's theorem for the double cosets $DC(Q_0)$

**Layer:** number fields.

Let $F$ be a number field whose ring of integers $\mathcal O_F$ is a principal ideal domain, $Q_0$ a quadratic form over
$\mathcal O_F$ in $n\ge3$ variables with $Q = Q_0\otimes F$ nondegenerate and **isotropic at every infinite place** of $F$,
$L = \mathcal O_F^n$, and assume O'Meara's local condition `LocalSpinorUnits Q v L` (every $\sigma\in O(V_\mathfrak p)$ with
unit spinor norm lies in $O'(V_\mathfrak p)\,O(L_\mathfrak p)$) at the primes $\mathfrak p\mid2\det H$ ($H$ the Hessian of
$Q_0$); at all other primes it holds automatically (`localSpinorUnits_of_unimodular`).

**Proves**
* **`dc_eq_dcL`, `subsingleton_DC`** (Eichler 1952; O'Meara 1963, 102:9, p. 304, and 104:5, p. 319): the **proper**
  classes in the genus, i.e. the double cosets
  $$SO(V)(F)\backslash SO(V)(\mathbb A_f)/SO(\hat L)\qquad(\texttt{DC }Q_0),$$
  form a single point, the class `dcL` of $L$ itself. *Proof:* write $b\in SO(V)(\mathbb A_f)$ as $b = \gamma k u$ with
  $\gamma = \tau_x\tau_y\in SO(V)(F)$, $k\in O'(V_{\mathbb A_f})$, $u\in O(\hat L)$ (`exists_spinorDecomp`: genus = spinor
  genus, with the rational factor a rotation), then $k = \delta k'$ with $\delta\in O'(V)$ and $k'\in O(\hat L)$ (strong
  approximation, `strongApproximationSpin`, unconditional). Since $\det\gamma = \det\delta = 1$ and $\det b = 1$, the
  integral factor $k'u$ is in $SO(\hat L)$. This is where improper elements enter: `LocalSpinorUnits` asks for
  $O'(V_\mathfrak p)O(L_\mathfrak p)$ to contain *every* $\sigma$ with unit spinor norm, including the improper ones, so each
  $O(L_\mathfrak p)$ contains an improper element; with that, the $SO$ and the $O$ double cosets agree.
* **`siegelIndefinite_oneClass`, `siegelIndefinite_oneClass_div`** (Siegel 1936, Hauptsatz for indefinite forms, one
  class in the genus): for totally real $F$, $N = k + 1\ge3$, $m\in\mathcal O_F\setminus0$ represented by $Q$ over $F$,
  $$\frac{c_\infty(m)\,\rho(L, m)}{v(L)} = |d_F|^{-(N-1)/2}\prod_\mathfrak p\beta_\mathfrak p(L, m),$$
  with $v(L)$ = `unitVolume`, $\rho(L, m)$ = `repMeasure` (at the class `dcL` of $L$). Conditional on the named
  inputs `AdelicSphereFibration`, `AdelicSphereDensities` and on $\tau(SO(V)) = \tau(SO(Q')) = 2$
  (`TamagawaNumberTwoAdelic`); `siegelIndefinite_oneClass_div_quaternary` discharges $\tau(SO(Q')) = 2$ for $N = 4$
  (`covolume_muTam_ternary`, every ternary form over every number field).
* `lintegral_theta_quaternary`: for every quaternary form over every number field, any signature,
  $\int_E\theta = 2\int\Phi\otimes1_{\hat L}\,d\sigma_{\mathbb A}$, conditional only on `AdelicSphereFibration`.
-/
import QuadFormsKB.Tamagawa.Indefinite.SiegelIndefinite
import QuadFormsKB.Tamagawa.Measure.Weil.SimilarTernary
import QuadFormsKB.Lattices.SAVectorsAnisotropic
import QuadFormsKB.Lattices.SpinorGlobal

open MeasureTheory NumberField IsDedekindDomain Matrix
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- **Spinor-kernel elements are rotations**: $O'(V)(K)\subseteq SO(V)(K)$ (a spinor word has even length). -/
theorem det_of_mem_spinorKernel (Q : QuadForm F n) {K : Type*} [Field K] [Algebra F K] [CharZero K]
    {g : orthGroup Q K} (hg : g ∈ spinorKernel Q K) : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
  obtain ⟨xs, ⟨hxa, hxe, -⟩, rfl⟩ := hg
  rw [← detHom_val, detHom_symmProd Q K xs hxa, hxe.neg_one_pow]

section DC

variable (Q₀ : QuadForm (𝓞 F) n)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-- **The proper class of $L = \mathcal O_F^n$** in `DC Q₀`: the double coset of $1$. -/
def dcL : DC Q₀ := ⟦1⟧

/-- **Every proper class in the genus is the class of $L$** (Eichler; O'Meara 1963, 102:9 and 104:5): under the
hypotheses $\mathcal O_F$ a principal ideal domain, $Q = Q_0\otimes F$ nondegenerate (`hQ`) in $n\ge3$ variables (`hn`),
isotropic at every infinite place (`hinf`), and `LocalSpinorUnits Q v L` at every finite prime (`hloc`), every
$b\in SO(V)(\mathbb A_f)$ is $b = \gamma\,b'$ with $\gamma\in SO(V)(F)$ and $b'\in SO(\hat L)$. -/
@[kb "omeara1963" "§102B, 102:9, p. 304; §104, 104:5, p. 319 (proper classes)"]
theorem dc_eq_dcL [IsPrincipalIdealRing (𝓞 F)] (hQ : (QF).Nondegenerate) (hn : 3 ≤ n)
    (hinf : ∀ w : InfinitePlace F, (QF).IsotropicIn w.Completion)
    (hloc : ∀ v, LocalSpinorUnits (QF) v (Tamagawa.stdLat F n)) (b : SOAf Q₀) :
    (⟦b⟧ : DC Q₀) = dcL Q₀ := by
  obtain ⟨γ, hγ, k, hk, u, hu, hh⟩ := exists_spinorDecomp (QF) hQ hn hinf _ hloc (b : OAf QF)
  have hind : IsIndefinite (QF) := by
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
    exact ⟨w, hinf w⟩
  obtain ⟨δ, hδ, hδk⟩ := strongApproximationSpin.approx (QF) hn hQ hind (Tamagawa.stdLat F n) k hk
  set w : OAf QF := (diagF QF δ)⁻¹ * k * u with hw_def
  have hw : w ∈ locStab QF (Tamagawa.stdLat F n) := (locStab QF _).mul_mem hδk hu
  have hb : (b : OAf QF) = diagF QF (γ * δ) * w := by
    rw [hh, hw_def, map_mul]; group
  have hdet : ((γ * δ : orthGroup QF F) : GL (Fin n) F).val.det = 1 := by
    rw [Subgroup.coe_mul, Units.val_mul, det_mul, hγ, det_of_mem_spinorKernel _ hδ, one_mul]
  let g : soSub QF F := ⟨γ * δ, hdet⟩
  have hwso : w ∈ soAf QF := by
    have e : w = (diagF QF (γ * δ))⁻¹ * (b : OAf QF) := by rw [hb]; group
    rw [e]
    exact (soAf QF).mul_mem ((soAf QF).inv_mem (finHom Q₀ g).2) b.2
  have hrel : (dcSetoid Q₀) 1 b := by
    refine ⟨diagSOAdele Q₀ g, ⟨g, rfl⟩, ⟨w, hwso⟩, Subgroup.mem_subgroupOf.mpr hw, ?_⟩
    apply Subtype.ext
    change (b : OAf QF) = diagF QF (γ * δ) * 1 * w
    rw [mul_one, hb]
  exact (Quotient.sound hrel).symm

/-- **One proper class in the genus** (Eichler; O'Meara 1963, 102:9 and 104:5): under the hypotheses of `dc_eq_dcL`,
$SO(V)(F)\backslash SO(V)(\mathbb A_f)/SO(\hat L)$ is a single point. -/
@[kb "omeara1963" "§102B, 102:9, p. 304; §104, 104:5, p. 319 (proper classes)"]
theorem subsingleton_DC [IsPrincipalIdealRing (𝓞 F)] (hQ : (QF).Nondegenerate) (hn : 3 ≤ n)
    (hinf : ∀ w : InfinitePlace F, (QF).IsotropicIn w.Completion)
    (hloc : ∀ v, LocalSpinorUnits (QF) v (Tamagawa.stdLat F n)) : Subsingleton (DC Q₀) :=
  ⟨fun i j => Quotient.inductionOn₂ i j fun b b' =>
    (dc_eq_dcL Q₀ hQ hn hinf hloc b).trans (dc_eq_dcL Q₀ hQ hn hinf hloc b').symm⟩

/-- `LocalSpinorUnits` at every prime from the bad primes $\mathfrak p\mid2\det H$ (`localSpinorUnits_of_unimodular`
elsewhere). -/
theorem localSpinorUnits_all (hn : 3 ≤ n)
    (hbad : ∀ v : HeightOneSpectrum (𝓞 F), ((2 : 𝓞 F) ∈ v.asIdeal ∨ Q₀.hessian.det ∈ v.asIdeal) →
      LocalSpinorUnits (QF) v (Tamagawa.stdLat F n)) (v : HeightOneSpectrum (𝓞 F)) :
    LocalSpinorUnits (QF) v (Tamagawa.stdLat F n) := by
  by_cases hb : (2 : 𝓞 F) ∈ v.asIdeal ∨ Q₀.hessian.det ∈ v.asIdeal
  · exact hbad v hb
  · push Not at hb
    exact localSpinorUnits_of_unimodular v Q₀ hb.1 hb.2 (by omega) _ (loc_intVec v)

/-- **`LocalSpinorUnits` from representations of all units** (any finite prime, dyadic or not): if $Q_0$ is
nondegenerate over $F$ (`hQ`) and every unit $u\in\mathfrak o_v^\times$ is $Q_0(y)$ for some $y\in\mathfrak o_v^n$ (`hrep`),
then every $\sigma\in O(V_v)$ with unit spinor norm lies in $O'(V_v)\,O(\mathfrak o_v^n)$. *Proof:* the symmetry
$\tau_y$ is an improper automorph of $\mathfrak o_v^n$ with spinor norm $u$ (`symm_mem_stdStab`); apply
`localSpinorUnits_of_improper`. -/
@[kb "omeara1963" "§92, 92:5, p. 249; §102B, 102:9, p. 304"]
theorem localSpinorUnits_of_unitReps (v : HeightOneSpectrum (𝓞 F)) (hQ : (QF).Nondegenerate)
    (hrep : ∀ u : v.adicCompletionIntegers F, IsUnit u →
      ∃ y : Fin n → v.adicCompletionIntegers F, (LocalDensity.NF.Qp v Q₀).eval y = u) :
    LocalSpinorUnits (QF) v (Tamagawa.stdLat F n) := by
  refine localSpinorUnits_of_improper (QF) v hQ _ fun u hu => ?_
  let u' : v.adicCompletionIntegers F := ⟨u, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hu.le⟩
  have hu' : IsUnit u' := by
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]; exact hu
  obtain ⟨y, hy⟩ := hrep u' hu'
  have hxstd : (fun i => (y i : v.adicCompletion F)) ∈ std v := fun i => by
    rw [neg_zero, WithZero.exp_zero]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (y i).2
  have hQx : (QF).evalIn (v.adicCompletion F) (fun i => (y i : v.adicCompletion F)) = u := by
    rw [Tamagawa.evalIn_coe_o v Q₀ y, hy]
  have hx0 : (QF).evalIn (v.adicCompletion F) (fun i => (y i : v.adicCompletion F)) ≠ 0 := by
    rw [hQx]; intro h; rw [h, map_zero] at hu; exact zero_ne_one hu
  have hs : symm (QF) (v.adicCompletion F) (fun i => (y i : v.adicCompletion F)) ∈ stdStab (QF) v :=
    symm_mem_stdStab v Q₀ hxstd (by rw [hQx, hu])
  have hL : symm (QF) (v.adicCompletion F) (fun i => (y i : v.adicCompletion F)) ∈
      locStabV (QF) v (Tamagawa.stdLat F n) :=
    (locStabV_eq_stdStab (QF) v (Tamagawa.stdLat F n) (loc_intVec v)).mpr hs
  refine ⟨_, hL, ?_, ?_⟩
  · ext; rw [detHom_val, symm_det (QF) _ hx0]; simp
  · rw [spinorNorm_symm (QF) _ hQ hx0, hQx]

/-- **One proper class in the genus, checking only the bad primes**: `subsingleton_DC` with `LocalSpinorUnits` assumed
only at the primes $\mathfrak p\mid2\det H$ (`hbad`). -/
@[kb "omeara1963" "§92, 92:5, p. 249; §102B, 102:9, p. 304; §104, 104:5, p. 319"]
theorem subsingleton_DC_of_bad [IsPrincipalIdealRing (𝓞 F)] (hQ : (QF).Nondegenerate) (hn : 3 ≤ n)
    (hinf : ∀ w : InfinitePlace F, (QF).IsotropicIn w.Completion)
    (hbad : ∀ v : HeightOneSpectrum (𝓞 F), ((2 : 𝓞 F) ∈ v.asIdeal ∨ Q₀.hessian.det ∈ v.asIdeal) →
      LocalSpinorUnits (QF) v (Tamagawa.stdLat F n)) : Subsingleton (DC Q₀) :=
  subsingleton_DC Q₀ hQ hn hinf (localSpinorUnits_all Q₀ hn hbad)

end DC

/-! ### Siegel's formula with one class in the genus -/

section Siegel

open QuadFormsKB.Tamagawa.Measure.SphereLeray NumberField.InfinitePlace

variable {k : ℕ} (Q₀ : QuadForm (𝓞 F) (k + 1)) (hQ : Q₀.Nondegenerate)

/-- **Siegel's formula for an indefinite form with one class in its genus** (Siegel 1936, Hauptsatz for indefinite
forms; Eichler 1952): let $F$ be a totally real number field with $\mathcal O_F$ a principal ideal domain, $Q_0$
nondegenerate over $\mathcal O_F$ in $N = k + 1\ge3$ variables, $Q$ isotropic at every real place (`hinf`), with
`LocalSpinorUnits` at the primes $\mathfrak p\mid2\det H$ (`hbad`), and $m\in\mathcal O_F\setminus0$ represented by $Q$
over $F$ (the base point of `A`). Given the inputs `AdelicSphereFibration` (`hA`), `AdelicSphereDensities` (`hβ`) and
$\tau(SO(V)) = \tau(SO(Q')) = 2$ (`hτ`, `hτ'`):
$$c_\infty(m)\,\rho(L, m) = |d_F|^{-(N-1)/2}\prod_\mathfrak p\beta_\mathfrak p(L, m)\cdot v(L),$$
$L = \mathcal O_F^N$, $v(L)$ = `unitVolume` and $\rho(L, m)$ = `repMeasure` at the proper class `dcL` of $L$, the only one
in its genus (`subsingleton_DC_of_bad`). -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (one class in the genus) [unverified]"]
theorem siegelIndefinite_oneClass [IsEmpty {w : InfinitePlace F // w.IsComplex}] [IsPrincipalIdealRing (𝓞 F)]
    (hk : 2 ≤ k) (hinf : ∀ w : InfinitePlace F, (Q₀.map (algebraMap (𝓞 F) F)).IsotropicIn w.Completion)
    (hbad : ∀ v : HeightOneSpectrum (𝓞 F), ((2 : 𝓞 F) ∈ v.asIdeal ∨ Q₀.hessian.det ∈ v.asIdeal) →
      LocalSpinorUnits (Q₀.map (algebraMap (𝓞 F) F)) v (Tamagawa.stdLat F (k + 1)))
    {m : 𝓞 F} (hm : (m : F) ≠ 0) {Q' : QuadForm (𝓞 F) k} {hQ' : Q'.Nondegenerate}
    {A : AdelicSphereData Q₀ (m : F) Q'} (hA : AdelicSphereFibration Q₀ hQ hQ' A)
    (hβ : AdelicSphereDensities Q₀ A (sigInf Q₀ (m : F)) (τInf Q₀ (m : F)))
    (hτ : TamagawaNumberTwoAdelic Q₀ hQ) (hτ' : TamagawaNumberTwoAdelic Q' hQ') :
    cInf (k := k) (m : F) * repMeasure Q₀ hQ (m : F) (totallyRealArchFibration Q₀ hQ hm (by omega)) (dcL Q₀) =
      ENNReal.ofReal (finDensityProduct Q₀ m) * unitVolume Q₀ hQ (dcL Q₀) := by
  have := subsingleton_DC_of_bad Q₀ (nondegenerate_map Q₀ hQ) (by omega) hinf hbad
  exact siegelIndefinite_classical_totallyReal_of_subsingleton Q₀ hQ (by omega) hm hA hβ hτ hτ' (dcL Q₀)

/-- **The ratio form**: under the hypotheses of `siegelIndefinite_oneClass`, $0 < v(L) < \infty$ and
$$\frac{c_\infty(m)\,\rho(L, m)}{v(L)} = |d_F|^{-(N-1)/2}\prod_\mathfrak p\beta_\mathfrak p(L, m).$$ -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (one class in the genus) [unverified]"]
theorem siegelIndefinite_oneClass_div [IsEmpty {w : InfinitePlace F // w.IsComplex}] [IsPrincipalIdealRing (𝓞 F)]
    (hk : 2 ≤ k) (hinf : ∀ w : InfinitePlace F, (Q₀.map (algebraMap (𝓞 F) F)).IsotropicIn w.Completion)
    (hbad : ∀ v : HeightOneSpectrum (𝓞 F), ((2 : 𝓞 F) ∈ v.asIdeal ∨ Q₀.hessian.det ∈ v.asIdeal) →
      LocalSpinorUnits (Q₀.map (algebraMap (𝓞 F) F)) v (Tamagawa.stdLat F (k + 1)))
    {m : 𝓞 F} (hm : (m : F) ≠ 0) {Q' : QuadForm (𝓞 F) k} {hQ' : Q'.Nondegenerate}
    {A : AdelicSphereData Q₀ (m : F) Q'} (hA : AdelicSphereFibration Q₀ hQ hQ' A)
    (hβ : AdelicSphereDensities Q₀ A (sigInf Q₀ (m : F)) (τInf Q₀ (m : F)))
    (hτ : TamagawaNumberTwoAdelic Q₀ hQ) (hτ' : TamagawaNumberTwoAdelic Q' hQ') :
    (cInf (k := k) (m : F) * repMeasure Q₀ hQ (m : F) (totallyRealArchFibration Q₀ hQ hm (by omega)) (dcL Q₀)) /
        unitVolume Q₀ hQ (dcL Q₀) =
      ENNReal.ofReal (finDensityProduct Q₀ m) := by
  have := subsingleton_DC_of_bad Q₀ (nondegenerate_map Q₀ hQ) (by omega) hinf hbad
  have hsum : ∑' i, unitVolume Q₀ hQ i = unitVolume Q₀ hQ (dcL Q₀) :=
    tsum_eq_single (dcL Q₀) fun j hj => absurd (Subsingleton.elim j (dcL Q₀)) hj
  rw [siegelIndefinite_oneClass Q₀ hQ hk hinf hbad hm hA hβ hτ hτ',
    ENNReal.mul_div_cancel_right (hsum ▸ tsum_unitVolume_ne_zero Q₀ hQ hτ)
      (hsum ▸ tsum_unitVolume_ne_top Q₀ hQ hτ)]

/-- **Quaternary forms ($N = 4$)**: `siegelIndefinite_oneClass_div` with $\tau(SO(Q')) = 2$ proved
(`covolume_muTam_ternary`, every ternary form over every number field), so only `AdelicSphereFibration`,
`AdelicSphereDensities` and $\tau(SO(V)) = 2$ remain. -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (one class in the genus; N = 4) [unverified]"]
theorem siegelIndefinite_oneClass_div_quaternary [IsEmpty {w : InfinitePlace F // w.IsComplex}]
    [IsPrincipalIdealRing (𝓞 F)] (Q₀ : QuadForm (𝓞 F) 4) (hQ : Q₀.Nondegenerate)
    (hinf : ∀ w : InfinitePlace F, (Q₀.map (algebraMap (𝓞 F) F)).IsotropicIn w.Completion)
    (hbad : ∀ v : HeightOneSpectrum (𝓞 F), ((2 : 𝓞 F) ∈ v.asIdeal ∨ Q₀.hessian.det ∈ v.asIdeal) →
      LocalSpinorUnits (Q₀.map (algebraMap (𝓞 F) F)) v (Tamagawa.stdLat F 4))
    {m : 𝓞 F} (hm : (m : F) ≠ 0) {Q' : QuadForm (𝓞 F) 3} {hQ' : Q'.Nondegenerate}
    {A : AdelicSphereData Q₀ (m : F) Q'} (hA : AdelicSphereFibration Q₀ hQ hQ' A)
    (hβ : AdelicSphereDensities Q₀ A (sigInf Q₀ (m : F)) (τInf Q₀ (m : F)))
    (hτ : TamagawaNumberTwoAdelic Q₀ hQ) :
    (cInf (k := 3) (m : F) * repMeasure Q₀ hQ (m : F) (totallyRealArchFibration Q₀ hQ hm (by omega)) (dcL Q₀)) /
        unitVolume Q₀ hQ (dcL Q₀) =
      ENNReal.ofReal (finDensityProduct Q₀ m) :=
  siegelIndefinite_oneClass_div Q₀ hQ (by norm_num) hinf hbad hm hA hβ hτ (covolume_muTam_ternary Q' hQ')

/-- **The theta integral of every quaternary form** ($N = 4$, every number field, every signature): given Weil's adelic
fibration over $T(m)$ (`AdelicSphereFibration`, input), for every fundamental domain $E$ of $SO(V)(F)$ in $SO(V)(\mathbb A)$,
$$\int_E\theta_{\Phi\otimes1_{\hat L}}\,d\mu = 2\int_{T(m)_{\mathbb A}}\Phi\otimes1_{\hat L}\,d\sigma_{\mathbb A}.$$
The factor $2 = \tau(SO(Q'))$ of the ternary stabilizer is proved (`covolume_muTam_ternary`). -/
@[kb "weil1982" "§4.5, p. 109; Thm 3.7.1 (m = 3), p. 65 [unverified page]"]
theorem lintegral_theta_quaternary (Q₀ : QuadForm (𝓞 F) 4) (hQ : Q₀.Nondegenerate) {m : F} (hm : m ≠ 0)
    {Q' : QuadForm (𝓞 F) 3} {hQ' : Q'.Nondegenerate} {A : AdelicSphereData Q₀ m Q'}
    (hA : AdelicSphereFibration Q₀ hQ hQ' A) {Φ : VInf F 4 → ℝ≥0∞} (hΦ : Measurable Φ) {E : Set (SOAdele Q₀)}
    (hE : IsFundamentalDomain (GammaSOAdele Q₀) E (muTam Q₀ hQ fun _ => 1)) :
    ∫⁻ g in E, thetaFn (ratA Q₀ m) (ratF Q₀ m) Φ (latHat F 4) g ∂muTam Q₀ hQ (fun _ => 1) =
      2 * ∫⁻ x, testFn Φ x.1 ∂A.σ := by
  rw [lintegral_theta_adelic Q₀ hQ (by norm_num) hm hA hΦ hE, covolume_muTam_ternary Q' hQ']

end Siegel

end QuadFormsKB.Tamagawa.Indefinite
