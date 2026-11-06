/-
# The height zeta function of $\mathbb P^1$ over a totally real field
**Layer:** analytic input for the convergence of the degree-$r$ Siegel Eisenstein series, over a totally real number field $F$.

**Results.**
* `summable_prod_pi`: if $\varphi : \alpha \to \mathbb R$ is nonnegative and summable and $\iota$ is finite, then
  $$x \mapsto \prod_{i\in\iota}\varphi(x_i)\quad\text{is summable on }\alpha^\iota.$$
* `summable_heightZeta`: for $z \in \mathbb H^d$ (one point per real place) and $\alpha > 2$,
  $$\sum_{u\in F}\Big(|N(z+u)|\cdot\prod_{v\nmid\infty}\max(1, |u|_v)\Big)^{-\alpha} < \infty,$$
  where $|N(z+u)| = \big|\prod_{w\mid\infty}(z_w + \sigma_w(u))\big|$ (`HilbertModular.eisDen (1, u) z`) and the product runs over the
  finite places $v$ (`HeightOneSpectrum (𝓞 F)`, the finite product `finprod`). This is Schanuel's height zeta function of $\mathbb P^1(F)$ with an
  archimedean twist; it is proved by the reduced-vector argument of `summable_norm_globalSec_archSecS`, comparing with the Hilbert Eisenstein majorant.

Sources: Schanuel, *Heights in number fields*, Bull. SMF 107 (1979) [unverified]; Weil, Acta Math. 113 (1965), Ch. II [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.SiegelWeil.Convergence

open IsDedekindDomain NumberField
open QuadFormsKB.Analysis QuadFormsKB.WeilRep QuadFormsKB.WeilRep.LocalData QuadFormsKB.HilbertModular

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

private theorem summable_prod_fin {α : Type*} {φ : α → ℝ} (h0 : ∀ x, 0 ≤ φ x) (hs : Summable φ) :
    ∀ n : ℕ, Summable fun x : Fin n → α => ∏ i, φ (x i)
  | 0 => by simpa using (Summable.of_finite (f := fun _ : Fin 0 → α => (1 : ℝ)))
  | n + 1 => by
      have ih := summable_prod_fin h0 hs n
      have h := Summable.mul_of_nonneg hs ih h0 (fun x => Finset.prod_nonneg fun i _ => h0 _)
      refine ((Fin.consEquiv (fun _ : Fin (n + 1) => α)).summable_iff).mp ?_
      refine h.congr fun p => ?_
      simp only [Function.comp, Fin.prod_univ_succ]
      rfl

/-- **Finite products of summable families.** If $\varphi : \alpha \to \mathbb R$ is nonnegative and summable and $\iota$ is a finite type, then
$x \mapsto \prod_{i\in\iota}\varphi(x_i)$ is summable on $\iota \to \alpha$. -/
theorem summable_prod_pi {α : Type*} {ι : Type*} [Fintype ι] {φ : α → ℝ} (h0 : ∀ x, 0 ≤ φ x)
    (hs : Summable φ) : Summable fun x : ι → α => ∏ i, φ (x i) := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  refine ((Equiv.arrowCongr e (Equiv.refl α)).symm.summable_iff).mp ?_
  refine (summable_prod_fin h0 hs (Fintype.card ι)).congr fun x => ?_
  simp only [Function.comp]
  rw [← e.prod_comp]
  simp [Equiv.arrowCongr]

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

local notation "ιO" => algebraMap (𝓞 F) F

/-- **The height zeta function of $\mathbb P^1(F)$ over a totally real field converges for $\alpha > 2$.** For $z \in \mathbb H^d$,
$$\sum_{u\in F}\Big(|N(z+u)|\prod_{v\nmid\infty}\max(1,|u|_v)\Big)^{-\alpha} < \infty.$$
*Proof:* as in `summable_norm_globalSec_archSecS`: with $(c,d) = t_u(1,u)$ the reduced vector of ratio $u$, the product formula gives
$\prod_v\max(1,|u|_v) \ge |N(c)|/E$ for a constant $E$ (`div_le_finprod_htV`), so the term is at most
$E^\alpha|N(cz+d)|^{-\alpha}$, summable over the orbits by `exists_summable_bound_rpow`. -/
theorem summable_heightZeta (z : InfinitePlace F → UpperHalfPlane) {α : ℝ} (hα : 2 < α) :
    Summable fun u : F => (‖HilbertModular.eisDen ((1 : F), u) (fun v => (z v : ℂ))‖ *
      ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), max 1 ‖algebraMap F (v.adicCompletion F) u‖) ^ (-α) := by
  classical
  have hα0 : 0 < α := by linarith
  have hrep : ∀ C : ClassGroup (𝓞 F), ∃ e : 𝓞 F, e ∈ repIdeal C ∧ e ≠ 0 :=
    fun C => Submodule.exists_mem_ne_zero_of_ne_bot (repIdeal_ne_bot C)
  choose e he he0 using hrep
  set E : ℝ := ∑ C, normAbs (ιO (e C)) with hE
  have heE : ∀ C, normAbs (ιO (e C)) ≤ E := fun C =>
    Finset.single_le_sum (f := fun C => normAbs (ιO (e C)))
      (fun C _ => Finset.prod_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ C)
  obtain ⟨B, hB, hBv⟩ := exists_pos_lt_min (y := imVec z) (imVec_pos z)
  obtain ⟨h, hsum, hbd⟩ := exists_summable_bound_rpow (eisWeight_redInd (F := F)) (σ := α) hα
    (∑ v, |(z v).re| + 1) hB
  have hz : ∀ v, z v ∈ UpperHalfPlane.verticalStrip (∑ v, |(z v).re| + 1) B := fun v => ⟨by
    have := Finset.single_le_sum (f := fun v => |(z v).re|) (fun _ _ => abs_nonneg _) (Finset.mem_univ v)
    linarith, (hBv v).le⟩
  refine ((hsum.comp_injective rho_injective).mul_left (E ^ α)).of_nonneg_of_le
    (fun u => Real.rpow_nonneg (mul_nonneg (norm_nonneg _) (finprod_nonneg fun v => zero_le_one.trans (le_max_left _ _))) _) fun u => ?_
  set c := redT u with hc
  have hc0 : c ≠ 0 := redT_ne_zero u
  set x : F × F := (c * 1, c * u) with hx
  have hred : IsRedVec x := isRedVec_redT u
  set C := cuspClass x.1 x.2
  have hmem : ιO (e C) ∈ cuspIdeal x.1 x.2 := by
    rw [hred.2]; exact (FractionalIdeal.mem_coeIdeal _).mpr ⟨e C, he C, rfl⟩
  obtain ⟨r, s', hrs⟩ := mem_cuspIdeal_iff.mp hmem
  have he0' : ιO (e C) ≠ 0 := (map_ne_zero_iff _ algebraMap_O_injective).mpr (he0 C)
  have hlow := div_le_finprod_htV u c (ιO (e C)) hc0 he0' ⟨r, s', by
    rw [hrs, Algebra.smul_def, Algebra.smul_def]; simp [x]⟩
  have hH : ∏ᶠ v : HeightOneSpectrum (𝓞 F), htV v (locSL v (wMat * nMat u)) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), max 1 ‖algebraMap F (v.adicCompletion F) u‖ := by
    refine finprod_congr fun v => ?_
    rw [htV_locSL_wMat_nMat]
  rw [hH] at hlow
  set H := ∏ᶠ v : HeightOneSpectrum (𝓞 F), max 1 ‖algebraMap F (v.adicCompletion F) u‖
  have hNe : 0 < normAbs (ιO (e C)) := normAbs_pos he0'
  have hNc : 0 < normAbs c := normAbs_pos hc0
  have hE0 : 0 < E := hNe.trans_le (heE C)
  set D := ‖eisDen ((1 : F), u) (fun v => (z v : ℂ))‖
  have hD : 0 < D := norm_pos_iff.mpr (eisDen_one_ne_zero u z)
  have hDx : ‖eisDen (rho u).out (fun v => (z v : ℂ))‖ = D * normAbs c := by
    obtain ⟨ε, hε⟩ := exists_smul_out x
    rw [rho, ← hε, eisDen_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_unitNorm, one_mul,
      show x = (c * ((1 : F), u).1, c * ((1 : F), u).2) from rfl, eisDen_smul_scalar, norm_mul, norm_prod, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hWo : ‖(fun x : F × F => if IsRedVec x then (1 : ℂ) else 0) (rho u).out‖ = 1 := by
    obtain ⟨ε, hε⟩ := exists_smul_out x
    rw [rho, ← hε]
    simp [isRedVec_unit_smul_iff, hred]
  have hho := hbd z hz (rho u)
  rw [hWo, one_mul, hDx] at hho
  have hlow' : D * normAbs c / E ≤ D * H := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left ((div_le_div_of_nonneg_left hNc.le hNe (heE C)).trans hlow) hD.le
  have hpos : 0 < D * normAbs c / E := by positivity
  have hkey : (D * H) ^ (-α) ≤ E ^ α * (D * normAbs c) ^ (-α) := by
    refine (Real.rpow_le_rpow_of_nonpos hpos hlow' (by linarith)).trans (le_of_eq ?_)
    rw [Real.div_rpow (by positivity) hE0.le, Real.rpow_neg hE0.le, div_inv_eq_mul, mul_comm]
  exact hkey.trans (mul_le_mul_of_nonneg_left hho (Real.rpow_nonneg hE0.le _))

end QuadFormsKB.SiegelWeil.Forms
