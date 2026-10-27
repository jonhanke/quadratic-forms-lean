/-
# Cassels, Chapter 9, §5: existence of genera (Theorem 1.2, the statement $\theta_n$, Lemma 5.1)

**Layer:** local forms `fp p : QuadForm ℤ_[p] n` for every prime $p$ (Cassels' $f_p$, "$\mathbb Z_p$-integral of
determinant $d$"), a real form `finf : QuadForm ℝ n` ($f_\infty$), a rational form `g : QuadForm ℚ n`; equivalence
over a ring `IsometricGL` (by $\mathrm{GL}_n$ of that ring); the determinant as $\det H = D$ ($D = 2^nd$ for Cassels'
$d$).

**Defines** `CasselsTheta n`, Cassels' statement $\theta_n$ (p. 141).

**Proves**
* `casselsTheta` ($\theta_n$ for every $n$), and Theorem 1.2 (`exists_form_of_local_forms`): given local forms of
  determinant $D \ne 0$ at every $p \le \infty$ and a rational form $g$ equivalent to all of them over $\mathbb Q_p$
  ($\mathbb R$), there is an integral form $f$ equivalent to each $f_p$ over $\mathbb Z_p$ (and over $\mathbb R$) and
  to $g$ over $\mathbb Q$;
* Lemma 5.1 (`casselsLemma51`): if moreover $a \ne 0$ is primitively represented by every $f_p$ and by $g$ over
  $\mathbb R$, the form $f$ can be chosen to represent $a$ primitively over $\mathbb Z$ (the hypothesis $\theta_{n-1}$ is
  kept, as in Cassels, though the proof does not need it: Cassels' Note).

*Generalization:* the local forms are only required to be integer-valued over $\mathbb Z_p$ (Cassels: classically
integral); classical integrality of $f_2$ passes to $f$.

*Proof (not Cassels' induction on $n$):* in $V = (\mathbb Q^n, g)$ take for each $p$ a $\mathbb Q_p$-isometry $\sigma_p$
from $(\mathbb Q_p^n, f_p)$ to $V_p$; for almost all $p$ ($p \nmid 2D$ and $g$ unimodular at $p$) both $g$ and $f_p$ are
unimodular over $\mathbb Z_p$ with determinants differing by a unit square, hence equivalent over $\mathbb Z_p$
(`Lattices.Nbr.isometricGL_of_unimodular_dvr`), and $\sigma_p$ may be taken in $\mathrm{GL}_n(\mathbb Z_p)$. The local
lattices $\sigma_p\mathbb Z_p^n$ are then almost all standard and glue to a lattice $L$ of $V$ (O'Meara 81:14,
`Lattices.LocFamily.existsUnique_loc_eq`); $L = \gamma\mathbb Z^n$ is free and $f(\mathbf x) = g(\gamma\mathbf x)$ does it.
Lemma 5.1 then follows from Theorem 5.1 (`exists_sameGenus_primRep`) applied to $f$.
-/
import QuadFormsKB.Literature.Cassels.Ch9Sec4
import QuadFormsKB.Literature.Cassels.Ch9Sec5

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel

variable {n : ℕ}

/-- **Cassels' statement $\theta_n$** (Ch. 9, §5, p. 141): *let $d \ne 0$ be a given integer and for each $p \ne \infty$
let $f_p(\mathbf x)$ be a $\mathbb Z_p$-integral form in $\mathbf x = (x_1, \dots, x_n)$ with determinant $d$. Suppose
that there exists a rational form $g(\mathbf x)$ which is $\mathbb Q_p$-equivalent to $f_p(\mathbf x)$ for each $p$. Then
there is an integral form $f(\mathbf x)$ which is $\mathbb Z_p$-equivalent to $f_p(\mathbf x)$ for each $p$ and
$\mathbb Q$-equivalent to $g$.* Forms integer-valued, determinant $\det H = D$ (module docstring). -/
@[kb "cassels1978" "Ch. 9, §5, statement θ_n, p. 141"]
def CasselsTheta (n : ℕ) : Prop :=
  ∀ D : ℤ, D ≠ 0 → ∀ fp : ∀ (p : ℕ) [Fact p.Prime], QuadForm ℤ_[p] n,
    (∀ (p : ℕ) [Fact p.Prime], (fp p).hessian.det = (D : ℤ_[p])) →
    ∀ g : QuadForm ℚ n,
      (∀ (p : ℕ) [Fact p.Prime], IsometricGL (g.map (Rat.castHom ℚ_[p])) ((fp p).map (PadicInt.Coe.ringHom))) →
    ∃ f : QuadForm ℤ n, (∀ (p : ℕ) [Fact p.Prime], IsometricGL (f.map (Int.castRingHom ℤ_[p])) (fp p)) ∧
      IsometricGL (f.map (Int.castRingHom ℚ)) g

end QuadFormsKB.Siegel

namespace QuadFormsKB.Lattices

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

variable {n : ℕ}

/-- The prime of `ℤ` below `v` is prime (as a `Fact`). -/
local instance factPrimesEquiv (v : HeightOneSpectrum (𝓞 ℚ)) :
    Fact (Rat.HeightOneSpectrum.primesEquiv v : ℕ).Prime :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- The ring isomorphism `ℤ_[p] ≃ 𝔬_v` for the place `v` over `p`. -/
def phiV (v : HeightOneSpectrum (𝓞 ℚ)) :
    ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)] ≃+* v.adicCompletionIntegers ℚ :=
  (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).symm.toAlgEquiv.toRingEquiv

/-- The ring isomorphism `ℚ_[p] ≃ F_v` for the place `v` over `p`. -/
def psiV (v : HeightOneSpectrum (𝓞 ℚ)) :
    ℚ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)] ≃+* v.adicCompletion ℚ :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm.toAlgEquiv.toRingEquiv

/-- `ψ_v` restricted to `ℤ_[p]` is `φ_v` followed by the inclusion `𝔬_v ⊆ F_v`. -/
theorem psiV_comp_coe (v : HeightOneSpectrum (𝓞 ℚ)) :
    (psiV v : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)] →+* v.adicCompletion ℚ).comp
      PadicInt.Coe.ringHom =
      (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)).comp (phiV v).toRingHom :=
  RingHom.ext fun _ => rfl

/-- **Local equivalence over `ℚ_p` transported to the completion `F_v`.** -/
theorem exists_sigma_of_padic (g : QuadForm ℚ n) (v : HeightOneSpectrum (𝓞 ℚ))
    (F : QuadForm ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)] n)
    (h : Siegel.IsometricGL (g.map (Rat.castHom ℚ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)]))
      (F.map PadicInt.Coe.ringHom)) :
    ∃ σ : GL (Fin n) (v.adicCompletion ℚ), ∀ y : Fin n → v.adicCompletion ℚ,
      g.evalIn (v.adicCompletion ℚ) (σ.val *ᵥ y) =
        (F.map (phiV v).toRingHom).evalIn (v.adicCompletion ℚ) y := by
  obtain ⟨σ, hσ⟩ := IsometricGL.map_ringEquiv (psiV v) h
  refine ⟨σ, fun y => ?_⟩
  have h1 := hσ y
  have e1 : (psiV v : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)] →+* v.adicCompletion ℚ).comp
      (Rat.castHom ℚ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)]) =
      algebraMap ℚ (v.adicCompletion ℚ) := RingHom.ext_rat _ _
  rw [QuadForm.map_map, QuadForm.map_map, e1, psiV_comp_coe] at h1
  rw [evalIn_eq_eval_map, evalIn_eq_eval_map, QuadForm.map_map]
  exact h1

section Good

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "Fv" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

/-- The integral form with the (integral) coefficients of `g` at `v`. -/
def intFormAt (g : QuadForm ℚ n) (hb : ∀ i j, Valued.v (algebraMap ℚ Fv (g.coeff i j)) ≤ 1) :
    QuadForm 𝔬 n :=
  QuadForm.ofUpper fun i j => toO v (algebraMap ℚ Fv (g.coeff i j)) (hb i j)

/-- The integral form `intFormAt` becomes `g` over `F_v`. -/
theorem intFormAt_map (g : QuadForm ℚ n) (hb : ∀ i j, Valued.v (algebraMap ℚ Fv (g.coeff i j)) ≤ 1) :
    (intFormAt v g hb).map (algebraMap 𝔬 Fv) = g.map (algebraMap ℚ Fv) := by
  ext i j
  simp only [intFormAt, QuadForm.map, QuadForm.ofUpper, Matrix.map_apply, Matrix.of_apply]
  split_ifs with h
  · rfl
  · rw [map_zero, g.upper (show j < i from not_le.mp h), map_zero]

/-- A form over `𝔬_v` with a unit Hessian determinant is not divisible by the uniformizer. -/
theorem not_pi_dvd_det {B : QuadForm 𝔬 n} (hB : Valued.v ((B.hessian.det : 𝔬) : Fv) = 1) :
    ¬ LocalDensity.NF.π v ∣ B.hessian.det := by
  intro hdvd
  have hunit : IsUnit B.hessian.det :=
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hB
  exact (LocalDensity.NF.irreducible_π v).not_isUnit (isUnit_of_dvd_unit hdvd hunit)

/-- The determinant of the Hessian of the base change. -/
theorem coe_det_hessian_map (B : QuadForm 𝔬 n) :
    ((B.hessian.det : 𝔬) : Fv) = (B.map (algebraMap 𝔬 Fv)).hessian.det := by
  rw [Siegel.hessian_map]
  exact RingHom.map_det (algebraMap 𝔬 Fv) B.hessian

/-- **At a good prime, the local isometry can be taken in `GL_n(𝔬_v)`** (unimodular classification). -/
theorem exists_sigma_stdStab (g : QuadForm ℚ n) (h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal)
    (hb : ∀ i j, Valued.v (algebraMap ℚ Fv (g.coeff i j)) ≤ 1)
    (hdet : Valued.v (algebraMap ℚ Fv g.hessian.det) = 1) (Fo : QuadForm 𝔬 n)
    (hFo : Valued.v ((Fo.hessian.det : 𝔬) : Fv) = 1) (σ0 : GL (Fin n) Fv)
    (h0 : ∀ y : Fin n → Fv, g.evalIn Fv (σ0.val *ᵥ y) = Fo.evalIn Fv y) :
    ∃ σ : GL (Fin n) Fv, (∀ y : Fin n → Fv, g.evalIn Fv (σ.val *ᵥ y) = Fo.evalIn Fv y) ∧
      locAct v σ (std v) = std v := by
  set Gv := intFormAt v g hb with hGv
  have hGmap := intFormAt_map v g hb
  have hGdet : Valued.v ((Gv.hessian.det : 𝔬) : Fv) = 1 := by
    rw [coe_det_hessian_map, hGmap, Siegel.hessian_map]
    exact (congrArg Valued.v (RingHom.map_det (algebraMap ℚ Fv) g.hessian).symm).trans hdet
  have hπ := LocalDensity.NF.irreducible_π v
  have hπ2 := LocalDensity.NF.π_not_dvd_two v h2
  have hGe : ∀ z : Fin n → Fv, Gv.evalIn Fv z = g.evalIn Fv z := fun z => by
    rw [evalIn_eq_eval_map Gv, evalIn_eq_eval_map g, hGmap]
  have hg' : ∀ x : Fin n → Fv, Fo.evalIn Fv x = Gv.evalIn Fv (σ0.val *ᵥ x) := by
    intro x
    rw [hGe, h0]
  obtain ⟨τ, hτ⟩ := Nbr.isometricGL_of_unimodular_of_isometricIn hπ hπ2 Fv Gv Fo
    (not_pi_dvd_det v hGdet) (not_pi_dvd_det v hFo) σ0 hg'
  have hc : Gv.compMat τ.val = Fo := QuadForm.ext_eval fun x => by rw [QuadForm.eval_compMat, hτ]
  refine ⟨GeneralLinearGroup.map (algebraMap 𝔬 Fv) τ, fun y => ?_, locAct_map_std v τ⟩
  change g.evalIn Fv (τ.val.map (algebraMap 𝔬 Fv) *ᵥ y) = _
  rw [evalIn_eq_eval_map g, ← hGmap, ← QuadForm.eval_compMat, QuadForm.map_compMat, hc,
    evalIn_eq_eval_map Fo]

/-- A form over `𝔬_v` evaluated at a vector of `𝔬_v^n` has valuation `≤ 1`. -/
theorem valued_evalIn_std_le_one (B : QuadForm 𝔬 n) {y : Fin n → Fv} (hy : y ∈ std v) :
    Valued.v (B.evalIn Fv y) ≤ 1 := by
  have hy' : ∀ i, Valued.v (y i) ≤ 1 := fun i => by simpa using hy i
  set y' : Fin n → 𝔬 := fun i => toO v (y i) (hy' i)
  have : B.evalIn Fv y = ((B.eval y' : 𝔬) : Fv) := by
    rw [evalIn_eq_eval_map]
    exact eval_map_comp (algebraMap 𝔬 Fv) B y'
  rw [this]
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (B.eval y').2

/-- `D` is a unit of `𝔬_v` when `D ∉ v`. -/
theorem valued_intCast_eq_one_of_not_mem {D : ℤ} (hD : (D : 𝓞 ℚ) ∉ v.asIdeal) :
    Valued.v (((D : 𝔬)) : Fv) = 1 := by
  have : (((D : 𝔬)) : Fv) = algebraMap (𝓞 ℚ) Fv (D : 𝓞 ℚ) := by simp
  rw [this]
  exact (valued_algebraMap_int v (D : 𝓞 ℚ)).trans (HeightOneSpectrum.intValuation_eq_one_iff.mpr hD)

/-- The prime `v` is *good* for `g` and `D`: odd, not dividing `D`, integral coefficients, unit determinant. -/
def GoodPrime (g : QuadForm ℚ n) (D : ℤ) : Prop :=
  (2 : 𝓞 ℚ) ∉ v.asIdeal ∧ (D : 𝓞 ℚ) ∉ v.asIdeal ∧ (∀ i j, v.valuation ℚ (g.coeff i j) ≤ 1) ∧
    v.valuation ℚ g.hessian.det = 1

end Good

/-- Almost every prime is good for `g` and `D`. -/
theorem eventually_goodPrime (g : QuadForm ℚ n) (hg0 : g.hessian.det ≠ 0) {D : ℤ} (hD : D ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, GoodPrime v g D := by
  have h2 := eventually_not_mem (F := ℚ) (d := (2 : 𝓞 ℚ)) two_ne_zero
  have hD' := eventually_not_mem (F := ℚ) (d := (D : 𝓞 ℚ)) (by exact_mod_cast hD)
  have hc : ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ∀ i j, v.valuation ℚ (g.coeff i j) ≤ 1 :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_valuation_le_one _
  have hd1 := eventually_valuation_le_one g.hessian.det
  have hd2 := eventually_valuation_le_one (g.hessian.det)⁻¹
  filter_upwards [h2, hD', hc, hd1, hd2] with v a b c d e
  refine ⟨a, b, c, le_antisymm d ?_⟩
  rw [map_inv₀] at e
  exact (inv_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hg0))).mp e


/-- The base change of `down Q₀` to any ring `R` is the base change of `Q₀` along any ring map. -/
theorem down_map_castHom (Q₀ : QuadForm (𝓞 ℚ) n) {R : Type*} [CommRing R] (ι : 𝓞 ℚ →+* R) :
    (Tamagawa.RatBridge.down Q₀).map (Int.castRingHom R) = Q₀.map ι := by
  have e : (Int.castRingHom R).comp (Tamagawa.RatBridge.eZ : 𝓞 ℚ →+* ℤ) = ι := by
    refine RingHom.ext fun x => ?_
    have h : (ι.comp (Tamagawa.RatBridge.eZ.symm : ℤ →+* 𝓞 ℚ)) (Tamagawa.RatBridge.eZ x) =
        (Int.castRingHom R) (Tamagawa.RatBridge.eZ x) :=
      RingHom.congr_fun (RingHom.ext_int _ _) _
    have h2 : ι x = (ι.comp (Tamagawa.RatBridge.eZ.symm : ℤ →+* 𝓞 ℚ)) (Tamagawa.RatBridge.eZ x) := by
      change ι x = ι (Tamagawa.RatBridge.eZ.symm (Tamagawa.RatBridge.eZ x))
      rw [RingEquiv.symm_apply_apply]
    exact (h2.trans h).symm
  rw [Tamagawa.RatBridge.down, QuadForm.map_map, e]

/-- **Theorem 1.2 at the level of the completions `𝔬_v`.** -/
theorem exists_form_of_local_o (g : QuadForm ℚ n) {D : ℤ} (hD : D ≠ 0)
    (Fo : ∀ v : HeightOneSpectrum (𝓞 ℚ), QuadForm (v.adicCompletionIntegers ℚ) n)
    (hFo : ∀ v, (Fo v).hessian.det = (D : v.adicCompletionIntegers ℚ))
    (hσ : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ σ : GL (Fin n) (v.adicCompletion ℚ),
      ∀ y : Fin n → v.adicCompletion ℚ, g.evalIn (v.adicCompletion ℚ) (σ.val *ᵥ y) =
        (Fo v).evalIn (v.adicCompletion ℚ) y) :
    ∃ f : QuadForm ℤ n, Siegel.IsometricGL (f.map (Int.castRingHom ℚ)) g ∧
      ∀ v : HeightOneSpectrum (𝓞 ℚ),
        Siegel.IsometricGL (f.map (Int.castRingHom (v.adicCompletionIntegers ℚ))) (Fo v) := by
  classical
  -- `g` is nondegenerate
  have hg0 : g.hessian.det ≠ 0 := by
    obtain ⟨v0⟩ := (nonempty_heightOneSpectrum : Nonempty (HeightOneSpectrum (𝓞 ℚ)))
    obtain ⟨σ0, h0⟩ := hσ v0
    have hiso : Siegel.IsometricGL (g.map (algebraMap ℚ (v0.adicCompletion ℚ)))
        ((Fo v0).map (algebraMap (v0.adicCompletionIntegers ℚ) (v0.adicCompletion ℚ))) :=
      ⟨σ0, fun y => by rw [← evalIn_eq_eval_map, ← evalIn_eq_eval_map, h0]⟩
    obtain ⟨P, hP⟩ := hiso.hessian_eq
    rw [Siegel.hessian_map, Siegel.hessian_map] at hP
    have hdet := congrArg Matrix.det hP
    have e1 : (g.hessian.map (algebraMap ℚ (v0.adicCompletion ℚ))).det =
        algebraMap ℚ (v0.adicCompletion ℚ) g.hessian.det := (RingHom.map_det _ _).symm
    have e2 : ((Fo v0).hessian.map (algebraMap (v0.adicCompletionIntegers ℚ) (v0.adicCompletion ℚ))).det =
        algebraMap (v0.adicCompletionIntegers ℚ) (v0.adicCompletion ℚ) (Fo v0).hessian.det :=
      (RingHom.map_det _ _).symm
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, e1, e2, hFo v0] at hdet
    have hDne : (((D : v0.adicCompletionIntegers ℚ)) : v0.adicCompletion ℚ) ≠ 0 := by
      have : (((D : v0.adicCompletionIntegers ℚ)) : v0.adicCompletion ℚ) =
          algebraMap ℚ (v0.adicCompletion ℚ) (D : ℚ) := by simp
      rw [this]; exact (map_ne_zero _).mpr (by exact_mod_cast hD)
    intro h0'
    rw [h0', map_zero, mul_zero, zero_mul] at hdet
    exact hDne hdet.symm
  -- improve the local isometries at the good primes
  have key : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ σ : GL (Fin n) (v.adicCompletion ℚ),
      (∀ y : Fin n → v.adicCompletion ℚ, g.evalIn (v.adicCompletion ℚ) (σ.val *ᵥ y) =
        (Fo v).evalIn (v.adicCompletion ℚ) y) ∧
      (GoodPrime v g D → locAct v σ (std v) = std v) := by
    intro v
    obtain ⟨σ0, h0⟩ := hσ v
    by_cases hv : GoodPrime v g D
    · obtain ⟨h2, hDv, hb, hdet⟩ := hv
      obtain ⟨σ, hσ1, hσ2⟩ := exists_sigma_stdStab v g h2
        (fun i j => by rw [valued_algebraMap]; exact hb i j)
        (by rw [valued_algebraMap]; exact hdet) (Fo v)
        (by rw [hFo v]; exact valued_intCast_eq_one_of_not_mem v hDv) σ0 h0
      exact ⟨σ, hσ1, fun _ => hσ2⟩
    · exact ⟨σ0, h0, fun h => absurd h hv⟩
  choose σ hσ1 hσ2 using key
  let fam : LocFamily ℚ n :=
    { M := fun v => locAct v (σ v) (std v)
      isLattice := fun v => locAct_isLattice (σ v) ((LocFamily.std (F := ℚ) (n := n)).isLattice v)
      eventually_std := by
        filter_upwards [eventually_goodPrime g hg0 hD] with v hv
        exact hσ2 v hv }
  have : IsPrincipalIdealRing (𝓞 ℚ) :=
    IsPrincipalIdealRing.of_surjective Rat.ringOfIntegersEquiv.symm.toRingHom
      Rat.ringOfIntegersEquiv.symm.surjective
  obtain ⟨γ, hγ⟩ := HilbertModular.exists_latOf_of_isPrincipalIdealRing
    (⟨fam.glue, fam.glue_isLattice⟩ : Lat ℚ n)
  have hloc : ∀ v, loc v (latOf γ) = locAct v (σ v) (std v) := fun v => by
    rw [← hγ]; exact fam.loc_glue v
  have hlocγ : ∀ v : HeightOneSpectrum (𝓞 ℚ), loc v (latOf γ) =
      locAct v (GeneralLinearGroup.map (algebraMap ℚ (v.adicCompletion ℚ)) γ) (std v) :=
    fun v => by rw [latOf, loc_glImage, loc_intVec]
  -- integrality
  have hint : IsIntegral g (latOf γ) := by
    intro x hx
    apply HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ
    intro v
    have hmem : locVec v x ∈ loc v (latOf γ) := locVec_mem_loc v hx
    rw [hloc] at hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    have hyx' : (σ v).val *ᵥ y = locVec v x := hyx
    have h1 := valued_evalIn_std_le_one v (Fo v) hy
    rw [← hσ1 v y, hyx', evalIn_locVec, valued_algebraMap] at h1
    exact h1
  refine ⟨Tamagawa.RatBridge.down (gramZ g γ hint), ?_, fun v => ?_⟩
  · rw [down_map_castHom _ (algebraMap (𝓞 ℚ) ℚ), gramZ_map]
    refine ⟨γ⁻¹, fun x => ?_⟩
    rw [eval_gramFormF_col, mulVec_inv_mulVec]
  · rw [down_map_castHom _ (algebraMap (𝓞 ℚ) (v.adicCompletionIntegers ℚ))]
    set γv := GeneralLinearGroup.map (algebraMap ℚ (v.adicCompletion ℚ)) γ with hγv
    have hP : locAct v (γv⁻¹ * σ v) (std v) = std v := by
      rw [locAct_mul, ← hloc v, hlocγ v, locAct_inv_locAct]
    obtain ⟨P0, hP0⟩ := exists_gl_o_of_locAct_eq v hP
    refine ⟨P0, fun x => Subtype.ext ?_⟩
    rw [coe_eval_gramZ_map]
    have e : (fun i => (((P0.val *ᵥ x) i : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ)) =
        P0.val.map (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) *ᵥ
          fun i => (x i : v.adicCompletion ℚ) := by
      funext i
      exact RingHom.map_mulVec (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) P0.val x i
    rw [e, show P0.val.map (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) =
      (γv⁻¹ * σ v).val from congrArg Units.val hP0]
    change g.evalIn _ (γv.val *ᵥ ((γv⁻¹ * σ v).val *ᵥ _)) = _
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_left, hσ1 v]
    exact (evalIn_eq_eval_map (Fo v) _).trans
      (eval_map_comp (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) (Fo v) x)

/-- Transport of a form equivalence over `𝔬_v` back to `ℤ_[p]`. -/
theorem isometricGL_padic_of_o (v : HeightOneSpectrum (𝓞 ℚ)) (f : QuadForm ℤ n)
    (F : QuadForm ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)] n)
    (h : Siegel.IsometricGL (f.map (Int.castRingHom (v.adicCompletionIntegers ℚ)))
      (F.map (phiV v).toRingHom)) :
    Siegel.IsometricGL (f.map (Int.castRingHom ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)])) F := by
  have h1 := IsometricGL.map_ringEquiv (phiV v).symm h
  have e1 : ((phiV v).symm : v.adicCompletionIntegers ℚ →+*
      ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)]).comp
      (Int.castRingHom (v.adicCompletionIntegers ℚ)) = Int.castRingHom _ := RingHom.ext_int _ _
  have e2 : ((phiV v).symm : v.adicCompletionIntegers ℚ →+*
      ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)]).comp (phiV v).toRingHom =
      RingHom.id _ := RingHom.ext fun x => by simp
  rw [QuadForm.map_map, QuadForm.map_map, e1, e2, QuadForm.map_id'] at h1
  exact h1

end QuadFormsKB.Lattices

namespace QuadFormsKB.Siegel

attribute [local instance] Lattices.factPrimesEquiv

variable {n : ℕ}

/-- **$\theta_n$ holds for every $n$** (Cassels, Ch. 9, §5, pp. 141–143; proof: module docstring). -/
@[kb "cassels1978" "Ch. 9, §5, θ_n, pp. 141–143"]
theorem casselsTheta (n : ℕ) : CasselsTheta n := by
  intro D hD fp hfp g hg
  let Fo : ∀ v : HeightOneSpectrum (𝓞 ℚ), QuadForm (v.adicCompletionIntegers ℚ) n := fun v =>
    (fp (Rat.HeightOneSpectrum.primesEquiv v : ℕ)).map (Lattices.phiV v).toRingHom
  obtain ⟨f, hf1, hf2⟩ := Lattices.exists_form_of_local_o g hD Fo
    (fun v => by
      change ((fp (Rat.HeightOneSpectrum.primesEquiv v : ℕ)).map (Lattices.phiV v).toRingHom).hessian.det = _
      have e : ((fp (Rat.HeightOneSpectrum.primesEquiv v : ℕ)).hessian.map (Lattices.phiV v).toRingHom).det =
          (Lattices.phiV v).toRingHom (fp (Rat.HeightOneSpectrum.primesEquiv v : ℕ)).hessian.det :=
        (RingHom.map_det _ _).symm
      rw [Siegel.hessian_map, e, hfp]
      simp)
    (fun v => Lattices.exists_sigma_of_padic g v _ (hg _))
  refine ⟨f, fun p _ => ?_, hf1⟩
  obtain ⟨v, hpv⟩ : ∃ v : HeightOneSpectrum (𝓞 ℚ), (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = p :=
    ⟨Rat.HeightOneSpectrum.primesEquiv.symm (⟨p, Fact.out⟩ : Nat.Primes),
      congrArg (fun q : Nat.Primes => (q : ℕ)) (Equiv.apply_symm_apply Rat.HeightOneSpectrum.primesEquiv _)⟩
  subst hpv
  exact Lattices.isometricGL_padic_of_o v f _ (hf2 v)

/-- Equivalence over `ℤ_p` to a form of nonzero determinant forces nonzero determinant. -/
theorem det_ne_zero_of_isometricGL_padic (p : ℕ) [Fact p.Prime] (f0 : QuadForm ℤ n) {D : ℤ} (hD : D ≠ 0)
    (F : QuadForm ℤ_[p] n) (hF : F.hessian.det = (D : ℤ_[p]))
    (h : IsometricGL (f0.map (Int.castRingHom ℤ_[p])) F) : f0.hessian.det ≠ 0 := by
  obtain ⟨P, hP⟩ := h.hessian_eq
  rw [Siegel.hessian_map] at hP
  have hdet := congrArg Matrix.det hP
  have e : (f0.hessian.map (Int.castRingHom ℤ_[p])).det = Int.castRingHom ℤ_[p] f0.hessian.det :=
    (RingHom.map_det _ _).symm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, e, hF] at hdet
  intro h0
  rw [h0, map_zero, mul_zero, zero_mul] at hdet
  exact hD (by exact_mod_cast hdet.symm)

/-- An invertible matrix over a local ring maps a vector with a unit coordinate to one with a unit coordinate. -/
theorem exists_isUnit_coord_mulVec {R : Type*} [CommRing R] [IsLocalRing R] (T : GL (Fin n) R)
    {x : Fin n → R} (hx : ∃ i, IsUnit (x i)) : ∃ i, IsUnit ((T.val *ᵥ x) i) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨i, hi⟩ := hx
  have e : x = T⁻¹.val *ᵥ (T.val *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have : x i ∈ IsLocalRing.maximalIdeal R := by
    rw [e]
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hcon j)
  exact this hi

/-- **Cassels, Theorem 1.2** (existence of genera, Ch. 9, p. 129): *let rational integers $n \ge 1$ and $d \ne 0$ be
given. For all $p$ (including $p = \infty$) let $f_p(\mathbf x)$ be a $\mathbb Z_p$-integral form of determinant $d$ in
the variables $\mathbf x = (x_1, \dots, x_n)$. Suppose that there exists a rational form $g(\mathbf x)$ which is
$\mathbb Q_p$-equivalent to $f_p(\mathbf x)$ for each $p$. Then there is a $\mathbb Z$-integral form $f(\mathbf x)$ which is
$\mathbb Z_p$-equivalent to $f_p(\mathbf x)$ for each $p$.* Here also $f$ is $\mathbb Q$-equivalent to $g$; forms
integer-valued, $\det H = D$ (module docstring). -/
@[kb "cassels1978" "Ch. 9, Thm. 1.2, p. 129 (proof: §5, p. 143)"]
theorem exists_form_of_local_forms {D : ℤ} (hD : D ≠ 0) (fp : ∀ (p : ℕ) [Fact p.Prime], QuadForm ℤ_[p] n)
    (hfp : ∀ (p : ℕ) [Fact p.Prime], (fp p).hessian.det = (D : ℤ_[p]))
    (finf : QuadForm ℝ n) (_hfinf : finf.hessian.det = D) (g : QuadForm ℚ n)
    (hg : ∀ (p : ℕ) [Fact p.Prime], IsometricGL (g.map (Rat.castHom ℚ_[p])) ((fp p).map (PadicInt.Coe.ringHom)))
    (hginf : IsometricGL (g.map (Rat.castHom ℝ)) finf) :
    ∃ f : QuadForm ℤ n, (∀ (p : ℕ) [Fact p.Prime], IsometricGL (f.map (Int.castRingHom ℤ_[p])) (fp p)) ∧
      IsometricGL (f.map (Int.castRingHom ℝ)) finf ∧ IsometricGL (f.map (Int.castRingHom ℚ)) g := by
  obtain ⟨f, hf, hfg⟩ := casselsTheta n D hD fp hfp g hg
  refine ⟨f, hf, ?_, hfg⟩
  have h1 := Tamagawa.RatBridge.isometricGL_map_hom (Rat.castHom ℝ) hfg
  rw [Lattices.QuadForm.map_map, RingHom.ext_int ((Rat.castHom ℝ).comp (Int.castRingHom ℚ))
    (Int.castRingHom ℝ)] at h1
  exact h1.trans hginf

/-- **Cassels, Lemma 5.1** (Ch. 9, pp. 141–143): *let $n \ge 2$ and suppose that $\theta_{n-1}$ holds. Let $d$,
$f_p(\mathbf x)$, $g(\mathbf x)$ be as in the hypotheses of $\theta_n$ and let $a \ne 0$ be a rational integer which is
represented primitively by each $f_p$ over $\mathbb Z_p$ and by $g(\mathbf x)$ over $\mathbb R = \mathbb Z_\infty$. Then
there exists an $f(\mathbf x)$ which has the properties required by $\theta_n$ and which represents $a$ primitively over
$\mathbb Z$.* -/
@[kb "cassels1978" "Ch. 9, Lemma 5.1, pp. 141–143"]
theorem casselsLemma51 (hn : 2 ≤ n) (_hθ : CasselsTheta (n - 1)) {D : ℤ} (hD : D ≠ 0)
    (fp : ∀ (p : ℕ) [Fact p.Prime], QuadForm ℤ_[p] n)
    (hfp : ∀ (p : ℕ) [Fact p.Prime], (fp p).hessian.det = (D : ℤ_[p])) (g : QuadForm ℚ n)
    (hg : ∀ (p : ℕ) [Fact p.Prime], IsometricGL (g.map (Rat.castHom ℚ_[p])) ((fp p).map (PadicInt.Coe.ringHom)))
    {a : ℤ} (ha : a ≠ 0)
    (hprim : ∀ (p : ℕ) [Fact p.Prime], ∃ x : Fin n → ℤ_[p], (∃ i, IsUnit (x i)) ∧ (fp p).eval x = a)
    (hreal : ∃ x : Fin n → ℝ, g.evalIn ℝ x = a) :
    ∃ f : QuadForm ℤ n, (∀ (p : ℕ) [Fact p.Prime], IsometricGL (f.map (Int.castRingHom ℤ_[p])) (fp p)) ∧
      IsometricGL (f.map (Int.castRingHom ℚ)) g ∧ ∃ x : Fin n → ℤ, Finset.univ.gcd x = 1 ∧ f.eval x = a := by
  obtain ⟨f0, hf0p, hf0g⟩ := casselsTheta n D hD fp hfp g hg
  have hf0 : f0.hessian.det ≠ 0 := det_ne_zero_of_isometricGL_padic 2 f0 hD (fp 2) (hfp 2) (hf0p 2)
  -- the real representation
  have hreal0 : ∃ x : Fin n → ℝ, f0.evalIn ℝ x = a := by
    obtain ⟨x, hx⟩ := hreal
    obtain ⟨P, hP⟩ := Tamagawa.RatBridge.isometricGL_map_hom (Rat.castHom ℝ) hf0g
    refine ⟨P.val *ᵥ x, ?_⟩
    have e1 : (f0.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ) = f0.map (Int.castRingHom ℝ) := by
      rw [Lattices.QuadForm.map_map, RingHom.ext_int ((Rat.castHom ℝ).comp (Int.castRingHom ℚ))
        (Int.castRingHom ℝ)]
    have e2 : g.map (Rat.castHom ℝ) = g.map (algebraMap ℚ ℝ) := rfl
    have := hP x
    rw [e1, e2, ← Lattices.evalIn_eq_eval_map, hx] at this
    rw [Lattices.evalIn_eq_eval_map]
    exact this
  -- the local primitive representations
  have hloc0 : ∀ (p : ℕ) [Fact p.Prime], (p = 2 ∨ (p : ℤ) ∣ f0.hessian.det ∨ (n = 2 ∧ (p : ℤ) ∣ a)) →
      ∃ x : Fin n → ℤ_[p], (∃ i, IsUnit (x i)) ∧ (f0.map (Int.castRingHom ℤ_[p])).eval x = a := by
    intro p _ _
    obtain ⟨x, hxu, hx⟩ := hprim p
    obtain ⟨T, hT⟩ := hf0p p
    exact ⟨T.val *ᵥ x, exists_isUnit_coord_mulVec T hxu, by rw [hT, hx]⟩
  obtain ⟨f', hsg, x, hx, hfx⟩ := exists_sameGenus_primRep f0 hn hf0 ha hreal0 hloc0
  refine ⟨f', fun p _ => ?_, ?_, x, hx, hfx⟩
  · exact (hsg.1 p).symm.trans (hf0p p)
  · exact (Lattices.isometricGL_rat_of_sameGenus f0 f' hsg.hessian_det_eq hf0 hsg).symm.trans hf0g

end QuadFormsKB.Siegel
