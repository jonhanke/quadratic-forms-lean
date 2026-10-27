/-
# $\tau(SO_3) = 2$ from Eichler's mass formula and the local factors of $\mathcal O^0$

**Layer:** $F$ totally real with $\mathcal O_F$ a PID.

**Assembly.** For a totally definite $D = (a,b)_F$, a maximal order $\mathcal O \supseteq \mathcal O_F\langle1,i,j,k\rangle$ with a trace-zero frame and
$Q_0 = Q_{\mathcal O^0}$:
$$\tau(SO(Q_0)) = \mu_{\mathrm{Tam}}(K_{SO})\cdot2^{-\#\mathrm{Ram}_f}\sum_{[J]}\frac1{[\Gamma_J:\mathcal O_F^\times]}\qquad(\texttt{TZFrame.tauSO\_eq}),$$
Eichler's closed form (`eichler_mass_formula'`), $\mathrm{vol}(SO_3(\mathbb R)) = \pi^2/(8\det^2)$, and the **local factors**
$$\alpha_v(\mathcal O_v^0) = (1-q_v^{-2})\cdot\varepsilon_v\cdot|8|_v^{-1}\,|D'|_v^{-3/2}\,|\rho|_v,\qquad \varepsilon_v = \tfrac{2}{1-q_v^{-1}}\ (v \in \mathrm{Ram}_f),\ 1\ \text{otherwise},$$
($D' = \det\frac12H_{Q_0}$, $\rho = \operatorname{re}e_0$) give $\tau = 2$ by the product formula $\prod_v|x|_v = |N(x)|^{-1}$ and
$\prod_v(1-q_v^{-2}) = \zeta_F(2)^{-1}$. The local factors are the named input `TraceZeroLocalFactors` (a statement about the local
maximal orders $\mathcal O_v$ only).

**Proves** `tauSO_eq_two_of_localFactors`, `ternaryTamagawaTwo_of_localFactors`.

Source: Weil 1982, §3.7(a) and Thm. 3.7.1 ($m = 3$); Voight 2021, Thm. 26.5.4 (Eichler) — the comparison is Weil's.
-/
import QuadFormsKB.Tamagawa.TernaryFrameExists

open NumberField IsDedekindDomain Matrix Quaternion Real

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.QuadForm QuadFormsKB.QuatZeta
  QuadFormsKB.HilbertModular QuadFormsKB.NFEuler

variable {F : Type} [Field F] [NumberField F]

/-- The $v$-adic absolute value $|x|_v$ of $x \in F$. -/
def absV (v : HeightOneSpectrum (𝓞 F)) (x : F) : ℝ := ‖NumberField.FinitePlace.embedding v x‖

/-- $D' = \det(\tfrac12H_{Q_0}) = \det H_{Q_0}/8$ for a ternary form over $\mathcal O_F$, in $F$. -/
def detHalf (Q₀ : QuadForm (𝓞 F) 3) : F := algebraMap (𝓞 F) F Q₀.hessian.det / 8

/-- **The local factor of the trace-zero lattice** (the value of $\alpha_v(\mathcal O_v^0)$ predicted by $\tau = 2$):
$(1-q^{-2})\,\varepsilon\,|8|_v^{-1}|D'|_v^{-3/2}|\rho|_v$, $\varepsilon = 2/(1-q^{-1})$ if $D$ ramifies at $v$, else $1$. -/
def tzFactor (v : HeightOneSpectrum (𝓞 F)) (ram : Prop) [Decidable ram] (D' ρ : F) : ℝ :=
  (1 - (normP v : ℝ) ^ (-(2 : ℝ))) * (if ram then 2 / (1 - (normP v : ℝ) ^ (-(1 : ℝ))) else 1) *
    (absV v 8)⁻¹ * absV v D' ^ (-(3 / 2 : ℝ)) * absV v ρ

variable [IsPrincipalIdealRing (𝓞 F)]

open Classical in
/-- **Input: the local densities of the trace-zero lattice of a local maximal order** (the local computation at the bad places). For every totally definite $(a,b)_F$, maximal $\mathcal O$ with trace-zero frame $e$ and $Q_0 = Q_{\mathcal O^0}$, and every
finite place $v$,
$$\alpha_v(Q_0, Q_0) = (1-q_v^{-2})\,\varepsilon_v\,|8|_v^{-1}\,|\det\tfrac12H_{Q_0}|_v^{-3/2}\,|\operatorname{re}e_0|_v.$$

Field:
- `factor`: the displayed identity (`tzFactor`).

*Hypothesis hygiene.* This is a statement about the local lattice $\mathcal O_v^0 \subseteq D_v$ alone (split: $\mathfrak{sl}_2(\mathfrak o_v)$ with
$-\det$; ramified: the trace-zero part of the valuation ring); it is not the global conclusion. At good primes it is the
classical $\alpha_v = 1 - q_v^{-2}$ (`volSO_good_odd`). -/
@[kb "voight2021" "§§13.3, 22.1 (local maximal orders, ternary lattice); Weil 1982, §3.7(a)"]
structure TraceZeroLocalFactors (F : Type) [Field F] [NumberField F] [IsPrincipalIdealRing (𝓞 F)] : Prop where
  factor : ∀ (a b : 𝓞 F) (ha : a ≠ 0) (hb : b ≠ 0), IsTotDefinite a b →
    ∀ (O : Subalgebra (𝓞 F) (QuatF F a b)), IsMaximalOrder (𝓞 F) F O → ∀ (fr : TZFrame O) (Q₀ : QuadForm (𝓞 F) 3),
      Q₀.map (algebraMap (𝓞 F) F) = fr.QF → ∀ v : HeightOneSpectrum (𝓞 F),
        LocalDensity.NF.siegelDensity v Q₀ Q₀ =
          tzFactor v (v ∈ ramFin ha hb) (detHalf Q₀) ((fr.e 0 : QuatF F a b).re)

/-! ### Products over the finite places -/

section Products

omit [IsPrincipalIdealRing (𝓞 F)] in
theorem absV_hasFiniteMulSupport {x : F} (hx : x ≠ 0) : (Function.mulSupport fun v => absV v x).Finite := by
  have h := NumberField.FinitePlace.hasFiniteMulSupport hx
  have : (Function.mulSupport fun v => absV v x) =
      NumberField.FinitePlace.equivHeightOneSpectrum '' (Function.mulSupport fun w : FinitePlace F => w x) := by
    ext v
    simp only [Function.mem_mulSupport, Set.mem_image]
    constructor
    · intro hv
      refine ⟨NumberField.FinitePlace.equivHeightOneSpectrum.symm v, ?_, by simp⟩
      rwa [NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply]
    · rintro ⟨w, hw, rfl⟩
      rwa [absV, ← NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply, Equiv.symm_apply_apply]
  rw [this]; exact h.image _

omit [IsPrincipalIdealRing (𝓞 F)] in
/-- **The product formula over the finite places:** $\prod_v|x|_v = |N_{F/\mathbb Q}(x)|^{-1}$ for $x \in F^\times$. -/
theorem tprod_absV {x : F} (hx : x ≠ 0) : ∏' v, absV v x = |((Algebra.norm ℚ x : ℚ) : ℝ)|⁻¹ := by
  have h2 := NumberField.FinitePlace.prod_eq_inv_abs_norm hx
  rw [← finprod_comp_equiv NumberField.FinitePlace.equivHeightOneSpectrum.symm] at h2
  simp only [NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply] at h2
  rw [tprod_eq_finprod (absV_hasFiniteMulSupport hx)]
  unfold absV
  rw [h2]
  push_cast; rfl

omit [IsPrincipalIdealRing (𝓞 F)] in
theorem absV_pos {v : HeightOneSpectrum (𝓞 F)} {x : F} (hx : x ≠ 0) : 0 < absV v x :=
  norm_pos_iff.2 ((map_ne_zero _).2 hx)

omit [IsPrincipalIdealRing (𝓞 F)] in
theorem tprod_absV_rpow {x : F} (hx : x ≠ 0) (s : ℝ) :
    ∏' v, absV v x ^ s = |((Algebra.norm ℚ x : ℚ) : ℝ)| ^ (-s) := by
  have hfin : (Function.mulSupport fun v => absV v x ^ s).Finite :=
    (absV_hasFiniteMulSupport hx).subset fun v hv h => hv (by simp only [h, Real.one_rpow])
  set T := (absV_hasFiniteMulSupport hx).toFinset
  have hsub : Function.mulSupport (fun v => absV v x) ⊆ T := by rw [Set.Finite.coe_toFinset]
  have hsub' : Function.mulSupport (fun v => absV v x ^ s) ⊆ T := by
    rw [Set.Finite.coe_toFinset]; exact fun v hv h => hv (by simp only [h, Real.one_rpow])
  have h3 := tprod_absV hx
  rw [tprod_eq_finprod (absV_hasFiniteMulSupport hx), finprod_eq_prod_of_mulSupport_subset _ hsub] at h3
  rw [tprod_eq_finprod hfin, finprod_eq_prod_of_mulSupport_subset _ hsub',
    Real.finset_prod_rpow _ _ (fun v _ => (absV_pos hx).le), h3, Real.inv_rpow (abs_nonneg _),
    Real.rpow_neg (abs_nonneg _)]

end Products

/-! ### The archimedean factor and the Gram determinant -/

section Gram

omit [IsPrincipalIdealRing (𝓞 F)]

/-- $\mathrm{vol}(SO_3(\mathbb R))$ for Gram determinant $d$: `archVolSO 3 d` $= \pi^2/(8d^2)$. -/
theorem archVolSO_three {d : ℝ} (hd : 0 < d) : archVolSO 3 d = π ^ 2 / (8 * d ^ 2) := by
  unfold archVolSO
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  have h12 : Real.Gamma ((((0 : ℕ) : ℝ) + 1) / 2) = Real.sqrt π := by
    norm_num [Real.Gamma_one_half_eq]
  have h1 : Real.Gamma ((((1 : ℕ) : ℝ) + 1) / 2) = 1 := by norm_num
  have h32 : Real.Gamma ((((2 : ℕ) : ℝ) + 1) / 2) = Real.sqrt π / 2 := by
    rw [show (((2 : ℕ) : ℝ) + 1) / 2 = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]; ring
  have p12 : π ^ ((((0 : ℕ) : ℝ) + 1) / 2) = Real.sqrt π := by
    rw [Real.sqrt_eq_rpow]; norm_num
  have p1 : π ^ ((((1 : ℕ) : ℝ) + 1) / 2) = π := by norm_num
  have p32 : π ^ ((((2 : ℕ) : ℝ) + 1) / 2) = π * Real.sqrt π := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' Real.pi_pos.le (by norm_num)]; norm_num
  rw [h12, h1, h32, p12, p1, p32]
  have hd2 : d ^ (-(((3 : ℕ) : ℝ) + 1) / 2) = (d ^ 2)⁻¹ := by
    rw [show (-(((3 : ℕ) : ℝ) + 1) / 2) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hd.le, Real.rpow_natCast]
  rw [hd2]
  have hs : 0 < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
  have hs2 : Real.sqrt π ^ 2 = π := Real.sq_sqrt Real.pi_pos.le
  have h8 : ((2 : ℝ) ^ (3 * (3 - 1) / 2)) = 8 := by norm_num
  rw [h8]
  field_simp

variable {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)} (fr : TZFrame O)

/-- $\det\operatorname{coord}(e) = \operatorname{re}(e_0)\cdot\det P$ (the first row of the coordinate matrix is $(\operatorname{re}e_0, 0, 0, 0)$). -/
theorem TZFrame.det_coordMat : (coordMat fun i => (fr.e i : QuatF F a b)).det = (fr.e 0 : QuatF F a b).re * fr.Pm.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have hz : ∀ j : Fin 3, (coordMat fun i => (fr.e i : QuatF F a b)) 0 j.succ = 0 := fun j => by
    simp [coordMat, fr.re_succ j]
  simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_mul]
  have hsub : (coordMat fun i => (fr.e i : QuatF F a b)).submatrix Fin.succ (Fin.succAbove 0) = fr.Pm := by
    ext r l; fin_cases r <;> rfl
  rw [hsub]; rfl

/-- $\det\tfrac12H_{Q_0} = \det(P)^2a^2b^2$ for $Q_0\otimes F = Q_{\mathcal O^0}$. -/
theorem TZFrame.detHalf_eq {Q₀ : QuadForm (𝓞 F) 3} (hQ : Q₀.map (algebraMap (𝓞 F) F) = fr.QF) :
    detHalf Q₀ = fr.Pm.det ^ 2 * (algebraMap (𝓞 F) F a) ^ 2 * (algebraMap (𝓞 F) F b) ^ 2 := by
  have h1 : algebraMap (𝓞 F) F Q₀.hessian.det = fr.QF.hessian.det := by
    rw [RingHom.map_det, ← hQ, QuadForm.hessian_map]; rfl
  have hH : (pureForm (algebraMap (𝓞 F) F a) (algebraMap (𝓞 F) F b)).hessian =
      Matrix.diagonal ![-2 * algebraMap (𝓞 F) F a, -2 * algebraMap (𝓞 F) F b,
        2 * (algebraMap (𝓞 F) F a * algebraMap (𝓞 F) F b)] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [QuadForm.hessian, pureForm, QuadForm.diag, Matrix.diagonal] <;> ring
  rw [detHalf, h1, TZFrame.QF, hessian_compMat, det_mul, det_mul, det_transpose, hH, det_diagonal,
    Fin.prod_univ_three]
  simp
  ring

theorem TZFrame.detHalf_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) {Q₀ : QuadForm (𝓞 F) 3}
    (hQ : Q₀.map (algebraMap (𝓞 F) F) = fr.QF) : detHalf Q₀ ≠ 0 := by
  rw [fr.detHalf_eq hQ]
  have ha' : algebraMap (𝓞 F) F a ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr ha
  have hb' : algebraMap (𝓞 F) F b ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hb
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ fr.det_Pm_ne_zero) (pow_ne_zero _ ha')) (pow_ne_zero _ hb')

/-- **The Gram determinant of $\mathcal O$ splits:** $\det(\langle e_i, e_j\rangle) = (\operatorname{re}e_0)^2\cdot\det\tfrac12H_{Q_0}$. -/
theorem TZFrame.det_gramMat {Q₀ : QuadForm (𝓞 F) 3} (hQ : Q₀.map (algebraMap (𝓞 F) F) = fr.QF) :
    (gramMat fun i => (fr.e i : QuatF F a b)).det = (fr.e 0 : QuatF F a b).re ^ 2 * detHalf Q₀ := by
  rw [gramMat_eq_coordMat, det_mul, det_mul, det_transpose, det_diagonal, fr.det_coordMat, fr.detHalf_eq hQ]
  simp [nrdDiag, Fin.prod_univ_four]
  ring

end Gram

/-! ### Assembly -/

section Assembly

omit [IsPrincipalIdealRing (𝓞 F)] in
theorem prod_absV_of_subset {x : F} (hx : x ≠ 0) {S : Finset (HeightOneSpectrum (𝓞 F))}
    (hS : ∀ v, absV v x ≠ 1 → v ∈ S) : ∏ v ∈ S, absV v x = |((Algebra.norm ℚ x : ℚ) : ℝ)|⁻¹ := by
  rw [← tprod_absV hx, tprod_eq_finprod (absV_hasFiniteMulSupport hx),
    finprod_eq_prod_of_mulSupport_subset _ (fun v hv => hS v hv)]

omit [IsPrincipalIdealRing (𝓞 F)] in
/-- $\prod_{\sigma : F\to\mathbb C}\|\sigma(x)\| = |N_{F/\mathbb Q}(x)|$. -/
theorem prod_norm_embeddings (x : F) : ∏ σ : F →ₐ[ℚ] ℂ, ‖σ x‖ = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  rw [← norm_prod, ← h]
  simp

omit [IsPrincipalIdealRing (𝓞 F)] in
/-- **The product of the predicted local factors:** for $D', \rho \in F^\times$,
$$\prod_v\alpha_v = \zeta_F(2)^{-1}\cdot\frac{2^{\#\mathrm{Ram}_f}}{\prod_{\mathrm{Ram}_f}(1-q_v^{-1})}\cdot|N(8)|\cdot|N(D')|^{3/2}\cdot|N(\rho)|^{-1}.$$ -/
theorem tprod_tzFactor {a b : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0) {_inst : ∀ v, Decidable (v ∈ ramFin ha hb)} {D' ρ : F}
    (hD : D' ≠ 0) (hρ : ρ ≠ 0) :
    ∏' v, tzFactor v (v ∈ ramFin ha hb) D' ρ =
      (dedekindZetaR F 2)⁻¹ * ((2 : ℝ) ^ (ramFin ha hb).card /
        ∏ v ∈ ramFin ha hb, (1 - (normP v : ℝ) ^ (-(1 : ℝ)))) *
        |((Algebra.norm ℚ (8 : F) : ℚ) : ℝ)| * |((Algebra.norm ℚ D' : ℚ) : ℝ)| ^ (3 / 2 : ℝ) *
        |((Algebra.norm ℚ ρ : ℚ) : ℝ)|⁻¹ := by
  set g : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    (if v ∈ (ramFin ha hb) then 2 / (1 - (normP v : ℝ) ^ (-(1 : ℝ))) else 1) * (absV v 8)⁻¹ * absV v D' ^ (-(3 / 2 : ℝ)) *
      absV v ρ
  have hfac : ∀ v, tzFactor v (v ∈ (ramFin ha hb)) D' ρ = (1 - (normP v : ℝ) ^ (-(2 : ℝ))) * g v := by
    intro v; unfold tzFactor; simp only [g]; ring
  have h8 : (8 : F) ≠ 0 := by norm_num
  haveI : DecidableEq (HeightOneSpectrum (𝓞 F)) := Classical.decEq _
  set S := (ramFin ha hb) ∪ (absV_hasFiniteMulSupport h8).toFinset ∪ (absV_hasFiniteMulSupport hD).toFinset ∪
    (absV_hasFiniteMulSupport hρ).toFinset
  have hmem : ∀ {x : F} (hx : x ≠ 0) v, absV v x ≠ 1 → v ∈ (absV_hasFiniteMulSupport hx).toFinset := by
    intro x hx v hv; rw [Set.Finite.mem_toFinset]; exact hv
  have h8S : ∀ v, absV v 8 ≠ 1 → v ∈ S := fun v hv => by
    simp only [S, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr (hmem h8 v hv)))
  have hDS : ∀ v, absV v D' ≠ 1 → v ∈ S := fun v hv => by
    simp only [S, Finset.mem_union]; exact Or.inl (Or.inr (hmem hD v hv))
  have hρS : ∀ v, absV v ρ ≠ 1 → v ∈ S := fun v hv => by
    simp only [S, Finset.mem_union]; exact Or.inr (hmem hρ v hv)
  have hRS : (ramFin ha hb) ⊆ S := fun v hv => by simp only [S, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl hv))
  have hg1 : ∀ v ∉ S, g v = 1 := by
    intro v hv
    have e8 : absV v 8 = 1 := by_contra fun h => hv (h8S v h)
    have eD : absV v D' = 1 := by_contra fun h => hv (hDS v h)
    have eρ : absV v ρ = 1 := by_contra fun h => hv (hρS v h)
    have eR : v ∉ (ramFin ha hb) := fun h => hv (hRS h)
    simp only [g, e8, eD, eρ, if_neg eR, Real.one_rpow]; norm_num
  have hP : HasProd (fun v => (1 - (normP v : ℝ) ^ (-(2 : ℝ))) * g v) ((dedekindZetaR F 2)⁻¹ * ∏ v ∈ S, g v) :=
    (hasProd_one_sub_rpow (F := F) (by norm_num : (1 : ℝ) < 2)).mul (hasProd_prod_of_ne_finset_one hg1)
  have hR : ∏ v ∈ S, (if v ∈ (ramFin ha hb) then 2 / (1 - (normP v : ℝ) ^ (-(1 : ℝ))) else 1) =
      (2 : ℝ) ^ (ramFin ha hb).card / ∏ v ∈ (ramFin ha hb), (1 - (normP v : ℝ) ^ (-(1 : ℝ))) := by
    rw [← Finset.prod_subset hRS (fun v _ hv => if_neg hv), Finset.prod_congr rfl (fun v hv => if_pos hv),
      Finset.prod_div_distrib, Finset.prod_const]
  have hpos : ∀ {x : F}, x ≠ 0 → ∀ v ∈ S, 0 ≤ absV v x := fun hx v _ => (absV_pos hx).le
  rw [tprod_congr hfac, hP.tprod_eq]
  simp only [g]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_inv_distrib,
    Real.finsetProd_rpow _ _ (hpos hD), hR, prod_absV_of_subset h8 h8S, prod_absV_of_subset hD hDS,
    prod_absV_of_subset hρ hρS, inv_inv, Real.inv_rpow (abs_nonneg _), ← Real.rpow_neg (abs_nonneg _), neg_neg]
  ring

variable [IsTotallyReal F] {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)} (fr : TZFrame O)

omit [IsPrincipalIdealRing (𝓞 F)] in
/-- The archimedean product: $\prod_\sigma\mathrm{vol}(SO(V_\sigma)) = \pi^{2d}\,8^{-d}\,|N(D')|^{-2}$. -/
theorem TZFrame.prod_archVolSO (ha : a ≠ 0) (hb : b ≠ 0) {Q₀ : QuadForm (𝓞 F) 3}
    (hQ : Q₀.map (algebraMap (𝓞 F) F) = fr.QF) :
    ∏ σ : F →ₐ[ℚ] ℂ, archVolSO 3 (detGram Q₀ σ) =
      (π ^ 2 / 8) ^ Module.finrank ℚ F / |((Algebra.norm ℚ (detHalf Q₀) : ℚ) : ℝ)| ^ 2 := by
  have hD := fr.detHalf_ne_zero ha hb hQ
  have hg : ∀ σ : F →ₐ[ℚ] ℂ, detGram Q₀ σ = ‖σ (detHalf Q₀)‖ := fun σ => by
    unfold detGram detHalf; norm_num
  have hpos : ∀ σ : F →ₐ[ℚ] ℂ, 0 < ‖σ (detHalf Q₀)‖ := fun σ => norm_pos_iff.2 ((map_ne_zero σ).2 hD)
  simp_rw [hg, fun σ => archVolSO_three (hpos σ)]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, AlgHom.card, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, AlgHom.card, Finset.prod_pow, prod_norm_embeddings, div_pow, div_div]

/-- The Eichler product: $\prod_v\sqrt{\det\sigma_v(A_{\mathcal O})} = |N(\rho)|\cdot|N(D')|^{1/2}$. -/
theorem TZFrame.prod_sqrt_det_gramMat (hdef : IsTotDefinite a b) {Q₀ : QuadForm (𝓞 F) 3}
    (hQ : Q₀.map (algebraMap (𝓞 F) F) = fr.QF) :
    ∏ v : InfinitePlace F, Real.sqrt ((gramMat fun i => (fr.e i : QuatF F a b)).map (realEmb F v)).det =
      |((Algebra.norm ℚ (fr.e 0 : QuatF F a b).re : ℚ) : ℝ)| *
        Real.sqrt |((Algebra.norm ℚ (detHalf Q₀) : ℚ) : ℝ)| := by
  set ρ := (fr.e 0 : QuatF F a b).re
  have hli := linearIndependent_basis_order fr.isOrder fr.e
  have hdet : ∀ v : InfinitePlace F, ((gramMat fun i => (fr.e i : QuatF F a b)).map (realEmb F v)).det =
      realEmb F v ρ ^ 2 * realEmb F v (detHalf Q₀) := fun v => by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, fr.det_gramMat hQ, map_mul, map_pow]
  have hDpos : ∀ v : InfinitePlace F, 0 < realEmb F v (detHalf Q₀) := fun v => by
    have h1 := ((isTotPosGram_gramMat hdef hli) v).det_pos
    rw [hdet v] at h1
    have h2 : 0 < realEmb F v ρ ^ 2 := pow_pos (abs_pos.2 ((map_ne_zero (realEmb F v)).2 fr.re_zero)) 2 |>.trans_eq (sq_abs _)
    exact pos_of_mul_pos_right h1 h2.le
  have hv : ∀ v : InfinitePlace F, Real.sqrt ((gramMat fun i => (fr.e i : QuatF F a b)).map (realEmb F v)).det =
      |realEmb F v ρ| * |realEmb F v (detHalf Q₀)| ^ (1 / 2 : ℝ) := fun v => by
    rw [hdet v, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_pos (hDpos v), Real.sqrt_eq_rpow]
  simp_rw [hv]
  rw [Finset.prod_mul_distrib, prod_abs_realEmb_eq, Real.finsetProd_rpow _ _ (fun v _ => abs_nonneg _),
    prod_abs_realEmb_eq, Real.sqrt_eq_rpow]

/-- **$\tau(SO(\mathcal O^0)) = 2$ from the local factors** ($F$ totally real, $\mathcal O_F$ a PID): for a totally definite
$(a,b)_F$, a maximal order $\mathcal O \supseteq \mathcal O_F\langle1,i,j,k\rangle$ with a trace-zero frame and $Q_0\otimes F = Q_{\mathcal O^0}$,
`TraceZeroLocalFactors F` gives $\tau(SO(Q_0)) = 2$. -/
@[kb "weil1982" "§3.7(a), Thm. 3.7.1 (m = 3), p. 62-65; Voight 2021, Thm. 26.5.4"]
theorem TZFrame.tauSO_eq_two_of_localFactors (I : TraceZeroLocalFactors F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hdef : IsTotDefinite a b) (hO : IsMaximalOrder (𝓞 F) F O) (hstd : stdOrder F a b ≤ O) (Q₀ : QuadForm (𝓞 F) 3)
    (hQ : Q₀.map (algebraMap (𝓞 F) F) = fr.QF) : tauSO Q₀ = 2 := by
  have hD := fr.detHalf_ne_zero ha hb hQ
  rw [fr.tauSO_eq ha hb hdef hO hstd Q₀ hQ, eichler_mass_formula' ha hb hdef hO hstd fr.e,
    fr.prod_sqrt_det_gramMat hdef hQ]
  unfold tamagawaK
  rw [fr.prod_archVolSO ha hb hQ, tprod_congr (fun v => I.factor a b ha hb hdef O hO fr Q₀ hQ v),
    tprod_tzFactor ha hb hD fr.re_zero, HilbertModular.card_infinitePlace]
  have h8 : Algebra.norm ℚ (8 : F) = 8 ^ Module.finrank ℚ F := by
    rw [show (8 : F) = algebraMap ℚ F 8 by simp, Algebra.norm_algebraMap]
  rw [h8]
  have hd : (0 : ℝ) < NumberField.discr F := AdditiveZeta.discr_pos
  rw [abs_of_pos hd]
  set n := Module.finrank ℚ F
  set ND := |((Algebra.norm ℚ (detHalf Q₀) : ℚ) : ℝ)|
  set Nρ := |((Algebra.norm ℚ (fr.e 0 : QuatF F a b).re : ℚ) : ℝ)|
  have hND : 0 < ND := abs_pos.2 (by exact_mod_cast (Algebra.norm_ne_zero_iff).2 hD)
  have hNρ : 0 < Nρ := abs_pos.2 (by exact_mod_cast (Algebra.norm_ne_zero_iff).2 fr.re_zero)
  have hZ : 0 < dedekindZetaR F 2 := lt_of_lt_of_le one_pos (one_le_dedekindZetaR (by norm_num))
  have hR : 0 < ∏ v ∈ ramFin ha hb, (1 - (normP v : ℝ) ^ (-(1 : ℝ))) := Finset.prod_pos fun v _ => by
    have h1 : (1 : ℝ) < normP v := by exact_mod_cast lt_of_lt_of_le (by norm_num) (two_le_normP v)
    have := Real.rpow_lt_one_of_one_lt_of_neg h1 (by norm_num : (-(1 : ℝ)) < 0)
    linarith
  have h32 : ND ^ (3 / 2 : ℝ) = ND * Real.sqrt ND := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hND.le (by norm_num)]; norm_num
  have hdd : (NumberField.discr F : ℝ) ^ (-(((3 : ℕ) : ℝ) * (((3 : ℕ) : ℝ) - 1) / 4)) = ((NumberField.discr F : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
    rw [← Real.rpow_neg hd.le]; norm_num
  rw [h32, hdd]
  have hs : 0 < Real.sqrt ND := Real.sqrt_pos.2 hND
  have hs2 : Real.sqrt ND ^ 2 = ND := Real.sq_sqrt hND.le
  have hδ : 0 < (NumberField.discr F : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hd _
  push_cast
  rw [abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
  have hπ : 0 < π := Real.pi_pos
  field_simp
  have h88 : (1 / 8 : ℝ) ^ n * 8 ^ n = 1 := by rw [← mul_pow]; norm_num
  linear_combination (π ^ (n * 2) * Real.sqrt ND ^ 2) * h88 + π ^ (n * 2) * hs2

open scoped ComplexOrder in
omit [IsPrincipalIdealRing (𝓞 F)] in
/-- $\langle -a,-b,ab\rangle$ totally positive definite $\Rightarrow$ $(a,b)_F$ totally definite. -/
theorem isTotDefinite_of_pureFormO {a b : 𝓞 F} (hpd : IsTotallyPosDef ((pureFormO a b).map (algebraMap (𝓞 F) F))) :
    IsTotDefinite a b := by
  intro σ
  let σ' : F →ₐ[ℚ] ℂ := (Complex.ofRealHom.comp σ).toRatAlgHom
  have key : ∀ i : Fin 3, 0 < σ (((pureFormO a b).map (algebraMap (𝓞 F) F)).eval (Pi.single i 1)) := by
    intro i
    have h := hpd (Pi.single i 1) (by simp)
    have h2 : (0 : ℂ) < ((σ (((pureFormO a b).map (algebraMap (𝓞 F) F)).eval (Pi.single i 1)) : ℝ) : ℂ) := h σ'
    exact_mod_cast h2
  have h0 := key 0
  have h1 := key 1
  rw [eval_single] at h0 h1
  simp [QuadForm.map, pureFormO, QuadForm.diag] at h0 h1
  exact ⟨h0, h1⟩

/-- **`TernaryTamagawaTwo F` from the local factors of the trace-zero lattices** ($F$ totally real, $\mathcal O_F$ a PID; no
hypothesis on $[F:\mathbb Q]$, so $F = \mathbb Q$ is included): every totally positive definite ternary form over $\mathcal O_F$ has
$\tau(SO) = 2$, given `TraceZeroLocalFactors F`. Route: Weil's reduction to $\langle -a,-b,ab\rangle$ (`ternaryTamagawaTwo_of_pureForm`),
a maximal order with a trace-zero frame, $\tau(\langle -a,-b,ab\rangle) = \tau(\mathcal O^0)$, and `TZFrame.tauSO_eq_two_of_localFactors`. -/
@[kb "weil1982" "§3.7(a), Thm. 3.7.1 (m = 3), p. 62-65"]
theorem ternaryTamagawaTwo_of_localFactors (I : TraceZeroLocalFactors F) : TernaryTamagawaTwo F := by
  refine LatChange.ternaryTamagawaTwo_of_pureForm fun a b ha hb hpd => ?_
  have hdef := isTotDefinite_of_pureFormO hpd
  have h2ab : algebraMap (𝓞 F) F (2 * a * b) ≠ 0 :=
    (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr (mul_ne_zero (mul_ne_zero two_ne_zero ha) hb)
  obtain ⟨O, hO, hstd⟩ := exists_isMaximalOrder_ge_stdOrder (R := 𝓞 F) (K := F) h2ab
  obtain ⟨fr⟩ := exists_TZFrame hO.1 hstd
  obtain ⟨Q₀, hQ⟩ := fr.exists_Q0
  unfold TamagawaNumberTwo
  rw [fr.tauSO_pureFormO_eq hstd hpd Q₀ hQ]
  exact fr.tauSO_eq_two_of_localFactors I ha hb hdef hO hstd Q₀ hQ

end Assembly

/-! ### The odd split places

At $v \nmid 2$ with $D_v$ split, $\mathcal O_v^0 \cong \mathfrak{sl}_2(\mathfrak o_v)$ with $\det$, whose Hessian determinant is $2$, so $Q_0$ is
unimodular at $v$ and $\alpha_v = 1 - q_v^{-2}$ (`volSO_good_odd`); and $|\operatorname{re}e_0|_v = 1$ since $1 = c_0\operatorname{re}e_0$
($1 \in \mathcal O$) and $2\operatorname{re}e_0 = \operatorname{trd}e_0 \in \mathcal O_F$. -/

section OddSplit

variable {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)} (fr : TZFrame O) (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- The form $-x_0^2 - x_1x_2$ ($= \det$ on $x_0h + x_1e_{12} + x_2e_{21} \in \mathfrak{sl}_2$). -/
def detSlForm : QuadForm Fv 3 where
  coeff := !![-1, 0, 0; 0, 0, -1; 0, 0, 0]
  upper := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [Fin.lt_def]

omit [IsPrincipalIdealRing (𝓞 F)] in
theorem eval_detSlForm (w : Fin 3 → Fv) : (detSlForm v).eval w = -w 0 ^ 2 - w 1 * w 2 := by
  simp only [detSlForm, QuadForm.evalIn, Fin.sum_univ_three, Algebra.algebraMap_self, RingHom.id_apply]
  simp (config := { decide := true })
  ring

omit [IsPrincipalIdealRing (𝓞 F)] in
theorem det_hessian_detSlForm : (detSlForm v).hessian.det = 2 := by
  simp only [detSlForm, QuadForm.hessian]
  rw [Matrix.det_fin_three]
  simp
  norm_num

/-- **At a split place, $Q_{\mathcal O^0}$ becomes $\det|_{\mathfrak{sl}_2}$ after an integral change of variables:**
$\det(H_{Q_{\mathcal O^0}})\cdot\det(Y)^2 = 2$ for some $Y \in M_3(\mathfrak o_v)$. -/
theorem TZFrame.exists_int_mat_split
    (φ : QuatV v a b ≃ₐ[v.adicCompletion F] Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
    (hφ : (localOrder (v := v) a b O).map ((φ : QuatV v a b →ₐ[v.adicCompletion F] _).restrictScalars
      (v.adicCompletionIntegers F)) = matOrder (v.adicCompletionIntegers F) (v.adicCompletion F)) :
    ∃ Y : Matrix (Fin 3) (Fin 3) 𝔬,
      (fr.QF.hessian.map (algebraMap F Fv)).det * ((Y.map (algebraMap 𝔬 Fv)).det) ^ 2 = 2 := by
  set Hm : Matrix (Fin 2) (Fin 2) Fv := !![1, 0; 0, -1]
  set z : Fin 3 → QuatV v a b := ![φ.symm Hm, E12 v φ, E21 v φ]
  have hz : ∀ k, z k ∈ fr.Ov0 v := by
    intro k; fin_cases k
    · show φ.symm Hm ∈ fr.Ov0 v
      rw [fr.mem_Ov0_iff, mem_localOrder_iff_split v φ hφ, re_eq_zero_iff_trace v φ, AlgEquiv.apply_symm_apply]
      refine ⟨(mem_matOrder).2 fun i j => ?_, by simp [Hm, Matrix.trace_fin_two]⟩
      fin_cases i <;> fin_cases j
      · exact ⟨1, by simp [Hm]⟩
      · exact ⟨0, by simp [Hm]⟩
      · exact ⟨0, by simp [Hm]⟩
      · exact ⟨-1, by simp [Hm]⟩
    · exact E12_mem fr v φ hφ
    · exact E21_mem fr v φ hφ
  have hy : ∀ k, ∃ y, fr.psiv v y = z k := fun k => fr.exists_psiv_eq v ((fr.mem_Ov0_iff v _).1 (hz k)).2
  choose y hyz using hy
  have hyint : ∀ k r, IsLocalization.IsInteger 𝔬 (y k r) := by
    intro k r
    have h := ((fr.mem_Ov0_iff_repr v (fr.psiv v (y k))).1 (by rw [hyz]; exact hz k)).2 r
    rw [fr.repr_psiv] at h
    simpa using h
  choose c hc using hyint
  refine ⟨Matrix.of fun r k => c k r, ?_⟩
  set Y := (Matrix.of fun r k => c k r).map (algebraMap 𝔬 Fv)
  set Sv := fr.QF.map (algebraMap F Fv)
  have hSv : ∀ w, Sv.eval w = nrd (fr.psiv v w) := fun w => by
    rw [TZFrame.psiv, nrd_psiP]
    show (fr.QF.map (algebraMap F Fv)).eval w = _
    rw [TZFrame.QF, ← QuadForm.map_compMat, pureForm_map, TZFrame.PGv_val]; rfl
  have hYw : ∀ w : Fin 3 → Fv, Y *ᵥ w = ∑ k, w k • y k := by
    intro w; ext r
    simp [Y, mulVec, dotProduct, Finset.sum_apply, hc, mul_comm]
  have hlin : ∀ w : Fin 3 → Fv, fr.psiv v (∑ k, w k • y k) = ∑ k, w k • z k := by
    intro w
    rw [Fin.sum_univ_three, Fin.sum_univ_three, ← hyz 0, ← hyz 1, ← hyz 2]
    simp only [TZFrame.psiv, psiP, mulVec_add, mulVec_smul, pure_add, pure_smul]
  have hval : ∀ w, (Sv.compMat Y).eval w = (detSlForm v).eval w := by
    intro w
    rw [eval_compMat, hSv, hYw, hlin, ← det_algEquiv φ, eval_detSlForm]
    simp only [Fin.sum_univ_three, map_add, map_smul, z, E12, E21, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, AlgEquiv.apply_symm_apply]
    simp [Hm, Matrix.det_fin_two]
    ring
  have hS : Sv.compMat Y = detSlForm v := eq_of_eval_eq hval
  have h2 := congrArg (fun S : QuadForm Fv 3 => S.hessian.det) hS
  simp only [hessian_compMat, det_mul, det_transpose, det_hessian_detSlForm] at h2
  rw [QuadForm.hessian_map] at h2
  linear_combination h2

/-- **At an odd split place $Q_0$ is unimodular:** $\det H_{Q_0} \notin \mathfrak p_v$. -/
theorem TZFrame.det_hessian_not_mem_split (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O)
    (hv : v ∉ ramFin ha hb) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) {Q₀ : QuadForm (𝓞 F) 3}
    (hQ : Q₀.map (algebraMap (𝓞 F) F) = fr.QF) : Q₀.hessian.det ∉ v.asIdeal := by
  obtain ⟨φ, hφ⟩ := split_of_not_mem_ramFin v ha hb hO hv
  obtain ⟨Y, hY⟩ := fr.exists_int_mat_split v φ hφ
  intro hmem
  have hH : algebraMap 𝔬 Fv (LocalDensity.NF.ι v Q₀.hessian.det) = (fr.QF.hessian.map (algebraMap F Fv)).det := by
    have e1 : algebraMap (𝓞 F) F Q₀.hessian.det = fr.QF.hessian.det := by
      rw [RingHom.map_det, ← hQ, QuadForm.hessian_map]; rfl
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, ← e1]; rfl
  have h1 : algebraMap 𝔬 Fv (LocalDensity.NF.ι v Q₀.hessian.det * Y.det ^ 2) = algebraMap 𝔬 Fv 2 := by
    rw [map_mul, map_pow, hH, RingHom.map_det, RingHom.mapMatrix_apply, hY, map_ofNat]
  have h1' := IsFractionRing.injective 𝔬 Fv h1
  have hd : LocalDensity.NF.π v ∣ LocalDensity.NF.ι v Q₀.hessian.det := by
    have := (LocalDensity.NF.π_pow_dvd_ι_iff v 1 Q₀.hessian.det).2 (by rwa [pow_one]); rwa [pow_one] at this
  exact not_dvd_two_of_good v h2 (h1' ▸ dvd_mul_of_dvd_left hd _)

omit [IsPrincipalIdealRing (𝓞 F)] in
theorem absV_int_le_one (y : 𝓞 F) : absV v (algebraMap (𝓞 F) F y) ≤ 1 :=
  NumberField.FinitePlace.norm_le_one (K := F) v y

omit [IsPrincipalIdealRing (𝓞 F)] in
theorem absV_int_eq_one {y : 𝓞 F} (hy : y ∉ v.asIdeal) : absV v (algebraMap (𝓞 F) F y) = 1 :=
  (NumberField.FinitePlace.norm_eq_one_iff_notMem (K := F) v y).2 hy

omit [IsPrincipalIdealRing (𝓞 F)] in
theorem absV_mul (x y : F) : absV v (x * y) = absV v x * absV v y := by
  simp only [absV, map_mul, norm_mul]

omit [IsPrincipalIdealRing (𝓞 F)] in
theorem absV_div (x y : F) : absV v (x / y) = absV v x / absV v y := by
  simp only [absV, map_div₀, norm_div]

omit [IsPrincipalIdealRing (𝓞 F)] in
theorem absV_eight (h2 : (2 : 𝓞 F) ∉ v.asIdeal) : absV v 8 = 1 := by
  have h8 : (8 : 𝓞 F) ∉ v.asIdeal := fun h =>
    h2 (v.isPrime.mem_of_pow_mem 3 (by norm_num; exact h))
  have := absV_int_eq_one v h8
  rwa [map_ofNat] at this

/-- **$\operatorname{re}e_0$ is a $v$-unit at odd $v$:** $1 = c_0\operatorname{re}e_0$ with $c_0 \in \mathcal O_F$ ($1 \in \mathcal O$), and
$2\operatorname{re}e_0 = \operatorname{trd}e_0 \in \mathcal O_F$. -/
theorem TZFrame.absV_re_eq_one (h2 : (2 : 𝓞 F) ∉ v.asIdeal) : absV v (fr.e 0 : QuatF F a b).re = 1 := by
  set ρ := (fr.e 0 : QuatF F a b).re
  have hc0 : algebraMap (𝓞 F) F (fr.e.repr ⟨1, O.one_mem⟩ 0) * ρ = 1 := by
    have h := congrArg Subtype.val (fr.e.sum_repr ⟨1, O.one_mem⟩)
    rw [Submodule.coe_sum, Fin.sum_univ_succ] at h
    have h' := congrArg QuaternionAlgebra.re h
    have e : ∀ i, ((fr.e.repr ⟨1, O.one_mem⟩ i • fr.e i : Subalgebra.toSubmodule O) : QuatF F a b).re =
        algebraMap (𝓞 F) F (fr.e.repr ⟨1, O.one_mem⟩ i) * (fr.e i : QuatF F a b).re := fun i => by
      rw [coe_smul_quatF, QuaternionAlgebra.re_smul, smul_eq_mul]
    simp only [Fin.sum_univ_three, QuaternionAlgebra.re_add, e, fr.re_succ, mul_zero, add_zero,
      QuaternionAlgebra.re_one] at h'
    exact h'
  obtain ⟨t, ht⟩ := (isInteger_trd_nrd fr.isOrder (fr.e 0).2).1
  have h1 := congrArg (absV v) hc0
  rw [absV_mul] at h1
  have h1' : absV v (1 : F) = 1 := by simp [absV]
  rw [h1'] at h1
  have hle := absV_int_le_one v (fr.e.repr ⟨1, O.one_mem⟩ 0)
  have hρ0 : 0 ≤ absV v ρ := norm_nonneg _
  have hge : 1 ≤ absV v ρ := by nlinarith
  have h2' : absV v (2 * ρ) ≤ 1 := by
    have := absV_int_le_one v t; rwa [ht, trd] at this
  rw [absV_mul, ← map_ofNat (algebraMap (𝓞 F) F) 2, absV_int_eq_one v h2, one_mul] at h2'
  exact le_antisymm h2' hge

/-- **The local factor at an odd split place:** for $v \nmid 2$, $v \notin \mathrm{Ram}_f$, $\alpha_v(Q_0, Q_0) = 1 - q_v^{-2}$, which is
`tzFactor` there ($|8|_v = |D'|_v = |\operatorname{re}e_0|_v = 1$). -/
theorem TZFrame.siegelDensity_odd_split (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O)
    (hv : v ∉ ramFin ha hb) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) {Q₀ : QuadForm (𝓞 F) 3}
    (hQ : Q₀.map (algebraMap (𝓞 F) F) = fr.QF) {_inst : Decidable (v ∈ ramFin ha hb)} :
    LocalDensity.NF.siegelDensity v Q₀ Q₀ =
      tzFactor v (v ∈ ramFin ha hb) (detHalf Q₀) ((fr.e 0 : QuatF F a b).re) := by
  have hd := fr.det_hessian_not_mem_split v ha hb hO hv h2 hQ
  have hnd : Q₀.Nondegenerate := fun h => hd (h ▸ Submodule.zero_mem _)
  rw [← volSO_eq v Q₀ hnd (by norm_num), volSO_good_odd v 1 Q₀ hnd h2 hd]
  unfold tzFactor
  rw [if_neg hv, fr.absV_re_eq_one v h2, absV_eight v h2, detHalf, absV_div, absV_int_eq_one v hd,
    absV_eight v h2]
  simp only [Finset.prod_range_one, div_one, Real.one_rpow, inv_one, mul_one]
  rw [Real.rpow_neg (by positivity), Real.rpow_two]

end OddSplit

/-! ### Reduction of the input to the bad places -/

section Bad

open Classical in
/-- **Input: the local densities of the trace-zero lattice at the bad places** (dyadic or ramified). As
`TraceZeroLocalFactors`, but only for finite places $v$ with $v \mid 2$ or $v \in \mathrm{Ram}_f(D)$:
$$\alpha_v(Q_0, Q_0) = (1-q_v^{-2})\,\varepsilon_v\,|8|_v^{-1}\,|\det\tfrac12H_{Q_0}|_v^{-3/2}\,|\operatorname{re}e_0|_v.$$

Field:
- `factor`: the displayed identity at the bad places.

*Hypothesis hygiene.* A statement about the local lattices $\mathcal O_v^0$ at finitely many places per algebra (split dyadic:
$\mathfrak{sl}_2(\mathfrak o_v)$ with $\det$; ramified: the trace-zero part of the valuation ring of $D_v$); not the global conclusion.
The remaining places are proved (`TZFrame.siegelDensity_odd_split`). -/
@[kb "voight2021" "§§13.3, 22.1 (local maximal orders at the dyadic and ramified places); Weil 1982, §3.7(a)"]
structure TraceZeroBadLocalFactors (F : Type) [Field F] [NumberField F] [IsPrincipalIdealRing (𝓞 F)] : Prop where
  factor : ∀ (a b : 𝓞 F) (ha : a ≠ 0) (hb : b ≠ 0), IsTotDefinite a b →
    ∀ (O : Subalgebra (𝓞 F) (QuatF F a b)), IsMaximalOrder (𝓞 F) F O → ∀ (fr : TZFrame O) (Q₀ : QuadForm (𝓞 F) 3),
      Q₀.map (algebraMap (𝓞 F) F) = fr.QF → ∀ v : HeightOneSpectrum (𝓞 F), ((2 : 𝓞 F) ∈ v.asIdeal ∨ v ∈ ramFin ha hb) →
        LocalDensity.NF.siegelDensity v Q₀ Q₀ =
          tzFactor v (v ∈ ramFin ha hb) (detHalf Q₀) ((fr.e 0 : QuatF F a b).re)

/-- **The trace-zero local factors at all places from those at the bad places** (the odd split places are proved). -/
theorem TraceZeroLocalFactors.of_bad (I : TraceZeroBadLocalFactors F) : TraceZeroLocalFactors F := by
  refine ⟨fun a b ha hb hdef O hO fr Q₀ hQ v => ?_⟩
  by_cases h : (2 : 𝓞 F) ∈ v.asIdeal ∨ v ∈ ramFin ha hb
  · exact I.factor a b ha hb hdef O hO fr Q₀ hQ v h
  · push_neg at h
    exact fr.siegelDensity_odd_split v ha hb hO h.2 h.1 hQ

/-- **`TernaryTamagawaTwo F` from the local factors at the dyadic and ramified places only** ($F$ totally real, $\mathcal O_F$ a
PID, $F = \mathbb Q$ included). -/
@[kb "weil1982" "§3.7(a), Thm. 3.7.1 (m = 3), p. 62-65"]
theorem ternaryTamagawaTwo_of_badLocalFactors [IsTotallyReal F] (I : TraceZeroBadLocalFactors F) :
    TernaryTamagawaTwo F :=
  ternaryTamagawaTwo_of_localFactors (TraceZeroLocalFactors.of_bad I)

end Bad

end QuadFormsKB.QuatOrder
