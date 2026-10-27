/-
# A worked example: $\langle1,1,1,-1\rangle$ over $\mathbb Q$ has one proper class in its genus

**Layer:** $F = \mathbb Q$, $Q_0 = \langle1,1,1,-1\rangle$ = `qEx` over $\mathcal O_{\mathbb Q}$ ($N = 4$, indefinite, signature
$(3,1)$), $L = \mathbb Z^4$, Hessian $H = 2\,\mathrm{diag}(1,1,1,-1)$ with $\det H = -16$. The only bad prime is $p = 2$,
which `localSpinorUnits_of_unimodular` does not cover.

**Proves**
* `exists_unit_eq_mul_sq` (the unit square classes of $\mathbb Q_2$): every $u\in\mathbb Z_2^\times$ is $u = c\,s^2$ with
  $c\in\{1, 3, 5, -1\}$ and $s\in\mathbb Z_2$. *Proof:* $u\equiv r\pmod 8$ for an odd integer $r$
  (`redHom_surjective`), $r\equiv c\pmod 8$, and a unit $\equiv1\pmod{8}$ is a square (local square theorem,
  `exists_sq_mod_iff_exists_sq`; here $2$ is a uniformizer, `ordTwo_eq_one`).
* **`localSpinorUnits_qEx_two`** (the local proof at $p = 2$): every $\sigma\in O(V_2)$ with unit spinor norm lies in
  $O'(V_2)\,O(\mathbb Z_2^4)$. *Proof:* the symmetries in $e_0$, $(1,1,1,0)$, $(1,2,0,0)$, $e_3$ (values $1, 3, 5, -1$),
  scaled by $s$, are improper automorphs of $\mathbb Z_2^4$ with every unit spinor norm (`localSpinorUnits_of_improper`).
* **`subsingleton_DC_qEx`**: $SO(V)(\mathbb Q)\backslash SO(V)(\mathbb A_f)/SO(\hat L)$ is a single point: the genus of
  $\langle1,1,1,-1\rangle$ has one proper class (unconditional).
* **`siegelIndefinite_qEx`**: for $m\in\mathbb Z\setminus0$ represented by $Q$ over $\mathbb Q$,
  $$\frac{c_\infty(m)\,\rho(L, m)}{v(L)} = \prod_p\beta_p(L, m),$$
  conditional on the named inputs `AdelicSphereFibration`, `AdelicSphereDensities` and on $\tau(SO(V)) = 2$
  (`TamagawaNumberTwoAdelic`; for this indefinite quaternary form it is not proved in the repository). The factor
  $\tau(SO(Q')) = 2$ of the ternary stabilizer is proved (`covolume_muTam_ternary`), and $|d_{\mathbb Q}| = 1$.
-/
import QuadFormsKB.Tamagawa.Indefinite.OneClass
import QuadFormsKB.Tamagawa.SiegelAllRanks
import QuadFormsKB.Tamagawa.RatHeadline3
import QuadFormsKB.LocalDensity.DyadicBad

open MeasureTheory NumberField IsDedekindDomain Matrix
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil
open QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.NF

/-! ### The form -/

/-- **$\langle1,1,1,-1\rangle$ over $\mathcal O_{\mathbb Q}$**: $Q_0(x) = x_0^2 + x_1^2 + x_2^2 - x_3^2$. -/
def qEx : QuadForm (𝓞 ℚ) 4 := QuadForm.diag ![1, 1, 1, -1]

local notation "QE" => qEx.map (algebraMap (𝓞 ℚ) ℚ)

theorem evalIn_qE (K : Type*) [Field K] [Algebra ℚ K] (x : Fin 4 → K) :
    (QE).evalIn K x = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 - x 3 ^ 2 := by
  simp [QuadForm.evalIn, QuadForm.map, qEx, QuadForm.diag, Fin.sum_univ_four, Matrix.diagonal_apply]
  ring

theorem hessian_det_qEx : qEx.hessian.det = -16 := by
  have : qEx.hessian = Matrix.diagonal (fun i => ![(1 : 𝓞 ℚ), 1, 1, -1] i + ![(1 : 𝓞 ℚ), 1, 1, -1] i) := by
    simp [qEx, QuadForm.hessian, QuadForm.diag, Matrix.diagonal_transpose, Matrix.diagonal_add]
  rw [this, Matrix.det_diagonal, Fin.prod_univ_four]
  norm_num

theorem nondegenerate_qEx : qEx.Nondegenerate := by
  rw [QuadForm.Nondegenerate, hessian_det_qEx]
  norm_num

/-- $Q$ is isotropic over every field: $Q(1, 0, 0, 1) = 0$. -/
theorem isotropicIn_qE (K : Type*) [Field K] [Algebra ℚ K] : (QE).IsotropicIn K :=
  ⟨![1, 0, 0, 1], fun h => by simpa using congrFun h 0, by rw [evalIn_qE]; simp⟩

/-! ### Unit square classes of $\mathbb Q_2$ -/

section Dyadic

variable {v : HeightOneSpectrum (𝓞 ℚ)} (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)

local notation "Fv" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

include h2

theorem natGenerator_eq_two : Rat.HeightOneSpectrum.natGenerator v = 2 := by
  have h := (RatHeadline3.intCast_mem_iff v 2).mp (by exact_mod_cast h2)
  have hp := Rat.HeightOneSpectrum.prime_natGenerator v
  have h' : Rat.HeightOneSpectrum.natGenerator v ∣ 2 := by exact_mod_cast h
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h'

/-- $2\notin\mathfrak p^2$: the prime $2$ is unramified in $\mathbb Q$. -/
theorem two_not_mem_sq : (2 : 𝓞 ℚ) ∉ v.asIdeal ^ 2 := by
  intro h
  have hmap := Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) h
  rw [Ideal.map_pow, ← Rat.HeightOneSpectrum.span_natGenerator, natGenerator_eq_two h2,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton, map_ofNat] at hmap
  norm_num at hmap

/-- $\operatorname{ord}_{\mathfrak p}2 = 1$. -/
theorem ordTwo_eq_one : ordTwo v = 1 := by
  obtain ⟨h1, h2'⟩ := ordTwo_spec v
  have hle : ordTwo v ≤ 1 := by
    by_contra hc
    apply two_not_mem_sq h2
    rw [← π_pow_dvd_ι_iff, map_ofNat]
    exact (pow_dvd_pow _ (by omega)).trans h1
  have hge : 1 ≤ ordTwo v := by
    by_contra hc
    apply h2'
    rw [show ordTwo v + 1 = 1 by omega, pow_one, ← map_ofNat (ι v), π_dvd_ι_iff]
    exact h2
  omega

/-- $\varpi\mid z$ in $\mathbb Z_2$ iff $2\mid z$, for $z\in\mathbb Z$. -/
theorem π_dvd_intCast_iff (z : ℤ) : π v ∣ (z : 𝔬) ↔ (2 : ℤ) ∣ z := by
  rw [← map_intCast (ι v), π_dvd_ι_iff, RatHeadline3.intCast_mem_iff, natGenerator_eq_two h2]
  norm_cast

/-- $\varpi^3\mid z$ in $\mathbb Z_2$ when $8\mid z$. -/
theorem π_pow_three_dvd_intCast {z : ℤ} (hz : (8 : ℤ) ∣ z) : π v ^ 3 ∣ (z : 𝔬) := by
  obtain ⟨t, rfl⟩ := hz
  rw [← map_intCast (ι v), π_pow_dvd_ι_iff]
  have e : (((8 * t : ℤ)) : 𝓞 ℚ) = 2 ^ 3 * (t : 𝓞 ℚ) := by push_cast; norm_num
  rw [e]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow h2 3)

/-- **Unit square classes of $\mathbb Q_2$**: every $u\in\mathbb Z_2^\times$ is $c\,s^2$ with $c\in\{1, 3, 5, -1\}$. -/
theorem exists_unit_eq_mul_sq {u : 𝔬} (hu : IsUnit u) :
    ∃ c : ℤ, (c = 1 ∨ c = 3 ∨ c = 5 ∨ c = -1) ∧ ∃ s : 𝔬, u = (c : 𝔬) * s ^ 2 := by
  obtain ⟨r, hr⟩ := redHom_surjective v 3 (Ideal.Quotient.mk _ u)
  have hr' : π v ^ 3 ∣ u - ι v r := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hr.symm)
  set z : ℤ := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) r
  have hzr : ι v r = (z : 𝔬) := by
    have : (z : 𝓞 ℚ) = r := by
      rw [← RatHeadline3.intEquiv_symm_intCast]
      exact RingEquiv.symm_apply_apply _ r
    rw [← this, map_intCast]
  rw [hzr] at hr'
  have hπu : ¬ π v ∣ u := fun h => (irreducible_π v).not_isUnit (isUnit_of_dvd_unit h hu)
  -- the integer `z` is odd
  have hz : ¬ (2 : ℤ) ∣ z := by
    intro hdvd
    apply hπu
    have h1 : π v ∣ u - (z : 𝔬) := (dvd_pow_self _ (by norm_num)).trans hr'
    have h2' : π v ∣ (z : 𝔬) := (π_dvd_intCast_iff h2 z).mpr hdvd
    simpa using dvd_add h1 h2'
  obtain ⟨c, hc, h8⟩ : ∃ c : ℤ, (c = 1 ∨ c = 3 ∨ c = 5 ∨ c = -1) ∧ (8 : ℤ) ∣ z - c := by
    have : z % 8 = 1 ∨ z % 8 = 3 ∨ z % 8 = 5 ∨ z % 8 = 7 := by omega
    rcases this with h | h | h | h
    · exact ⟨1, by norm_num, by omega⟩
    · exact ⟨3, by norm_num, by omega⟩
    · exact ⟨5, by norm_num, by omega⟩
    · exact ⟨-1, by norm_num, by omega⟩
  have hcodd : ¬ (2 : ℤ) ∣ c := by rcases hc with rfl | rfl | rfl | rfl <;> norm_num
  have h3 : π v ^ 3 ∣ (c : 𝔬) * 1 ^ 2 - u := by
    have e : (c : 𝔬) * 1 ^ 2 - u = -((u - (z : 𝔬)) + ((z - c : ℤ) : 𝔬)) := by push_cast; ring
    rw [e, dvd_neg]
    exact dvd_add hr' (π_pow_three_dvd_intCast h2 h8)
  have he := ordTwo_spec v
  rw [ordTwo_eq_one h2] at he
  obtain ⟨s, hs⟩ := (DVR.exists_sq_mod_iff_exists_sq (irreducible_π v)
    (by simpa [pow_one] using he.1) (two_ne_zero' v) 1 he
    (fun h => hcodd ((π_dvd_intCast_iff h2 c).mp h)) hπu).mp ⟨1, by simpa using h3⟩
  exact ⟨c, hc, s, hs.symm⟩

omit h2 in
/-- Vectors $y\in\mathbb Z^4$ with $Q(y) = c$ for the four unit classes $c\in\{1, 3, 5, -1\}$:
$e_0$, $(1,1,1,0)$, $(1,2,0,0)$, $e_3$. -/
theorem exists_vec_eq (c : ℤ) (hc : c = 1 ∨ c = 3 ∨ c = 5 ∨ c = -1) :
    ∃ y : Fin 4 → ℤ, y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 - y 3 ^ 2 = c := by
  rcases hc with rfl | rfl | rfl | rfl
  · exact ⟨![1, 0, 0, 0], by simp⟩
  · exact ⟨![1, 1, 1, 0], by simp⟩
  · exact ⟨![1, 2, 0, 0], by simp⟩
  · exact ⟨![0, 0, 0, 1], by simp⟩

/-- **The local condition at $p = 2$ for $\langle1,1,1,-1\rangle$** (the dyadic case, not covered by
`localSpinorUnits_of_unimodular`): every $\sigma\in O(V_2)$ with unit spinor norm lies in $O'(V_2)\,O(\mathbb Z_2^4)$.
*Proof:* for a unit $u = c\,s^2$ (`exists_unit_eq_mul_sq`) the symmetry in $s\,y_c$ ($Q(y_c) = c$, `exists_vec_eq`) is
an improper automorph of $\mathbb Z_2^4$ with spinor norm $u$ (`localSpinorUnits_of_unitReps`). -/
@[kb "omeara1963" "§92, 92:5, p. 249 (dyadic case by hand); §102B, 102:9, p. 304"]
theorem localSpinorUnits_qEx_two : LocalSpinorUnits (QE) v (Tamagawa.stdLat ℚ 4) := by
  refine localSpinorUnits_of_unitReps qEx v (nondegenerate_map qEx nondegenerate_qEx) fun u hu => ?_
  obtain ⟨c, hc, s, hs⟩ := exists_unit_eq_mul_sq h2 hu
  obtain ⟨y, hy⟩ := exists_vec_eq c hc
  refine ⟨fun i => s * (y i : 𝔬), ?_⟩
  have hy' : ((y 0 : 𝔬)) ^ 2 + (y 1 : 𝔬) ^ 2 + (y 2 : 𝔬) ^ 2 - (y 3 : 𝔬) ^ 2 = (c : 𝔬) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : 𝔬)) hy
  rw [hs, ← hy', qEx, Qp_diag]
  simp [QuadForm.eval, QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_four, Matrix.diagonal_apply]
  ring

end Dyadic

/-! ### One proper class, and Siegel's formula -/

/-- The bad primes of $\langle1,1,1,-1\rangle$: $\mathfrak p\mid2\det H = -32$ only for $p = 2$. -/
theorem localSpinorUnits_qEx_bad (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : (2 : 𝓞 ℚ) ∈ v.asIdeal ∨ qEx.hessian.det ∈ v.asIdeal) :
    LocalSpinorUnits (QE) v (Tamagawa.stdLat ℚ 4) := by
  refine localSpinorUnits_qEx_two ?_
  rcases hv with h | h
  · exact h
  · rw [hessian_det_qEx, Ideal.neg_mem_iff, show (16 : 𝓞 ℚ) = 2 ^ 4 by norm_num] at h
    exact v.isPrime.mem_of_pow_mem 4 h

/-- **The genus of $\langle1,1,1,-1\rangle$ has one proper class**: $SO(V)(\mathbb Q)\backslash SO(V)(\mathbb A_f)/SO(\hat L)$
is a single point (Eichler; unconditional). -/
@[kb "omeara1963" "§102B, 102:9, p. 304; §104, 104:5, p. 319 (example ⟨1,1,1,−1⟩)"]
theorem subsingleton_DC_qEx : Subsingleton (DC qEx) :=
  subsingleton_DC_of_bad qEx (nondegenerate_map qEx nondegenerate_qEx) (by norm_num)
    (fun w => isotropicIn_qE w.Completion) localSpinorUnits_qEx_bad

/-- $\mathbb Q$ has no complex places. -/
instance isEmpty_isComplex_rat : IsEmpty {w : InfinitePlace ℚ // w.IsComplex} :=
  ⟨fun w => (InfinitePlace.not_isComplex_iff_isReal.mpr (IsTotallyReal.isReal w.1)) w.2⟩

/-- **Siegel's formula for $\langle1,1,1,-1\rangle$** (Siegel 1936, Hauptsatz for indefinite forms, one class in the
genus): for $m\in\mathbb Z\setminus0$ represented by $Q$ over $\mathbb Q$ (base point of `A`), with ternary stabilizer
form $Q'$,
$$\frac{c_\infty(m)\,\rho(L, m)}{v(L)} = \prod_p\beta_p(L, m)\qquad(|d_{\mathbb Q}| = 1),$$
conditional on the named inputs `AdelicSphereFibration` (`hA`), `AdelicSphereDensities` (`hβ`) and on
$\tau(SO(V)) = 2$ (`hτ`). One proper class (`subsingleton_DC_qEx`) and $\tau(SO(Q')) = 2$ are proved. -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (example ⟨1,1,1,−1⟩) [unverified]"]
theorem siegelIndefinite_qEx {m : 𝓞 ℚ} (hm : (m : ℚ) ≠ 0) {Q' : QuadForm (𝓞 ℚ) 3} {hQ' : Q'.Nondegenerate}
    {A : AdelicSphereData qEx (m : ℚ) Q'} (hA : AdelicSphereFibration qEx nondegenerate_qEx hQ' A)
    (hβ : AdelicSphereDensities qEx A (sigInf qEx (m : ℚ)) (τInf qEx (m : ℚ)))
    (hτ : TamagawaNumberTwoAdelic qEx nondegenerate_qEx) :
    (cInf (k := 3) (m : ℚ) *
        repMeasure qEx nondegenerate_qEx (m : ℚ) (totallyRealArchFibration qEx nondegenerate_qEx hm (by norm_num))
          (dcL qEx)) / unitVolume qEx nondegenerate_qEx (dcL qEx) =
      ENNReal.ofReal (∏' p : HeightOneSpectrum (𝓞 ℚ), NF.localDensity p qEx m) := by
  rw [siegelIndefinite_oneClass_div_quaternary qEx nondegenerate_qEx (fun w => isotropicIn_qE w.Completion)
    localSpinorUnits_qEx_bad hm hA hβ hτ, finDensityProduct, Rat.numberField_discr]
  simp

end QuadFormsKB.Tamagawa.Indefinite
