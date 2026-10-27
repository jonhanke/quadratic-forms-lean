/-
# $K_N\subseteq U^{(M)}_v = \varphi(Y^{(M)})$

**Layer:** as in `GnatNSWinIndex`: a number field $F$, $K = F(\delta)$, a finite place $v$ (any), $Y = Y^{(M)}$ at levels $M$,
$K_N\le SO(\langle1,-ad,-bd,abd\rangle)(F_v)$ the principal congruence subgroup.

**`congSub_le_nsUSub`**: for $N$ large compared with $M$ (`WinHyp` and $M_w\le e_w(N - e_a - e_b - e_d - 2s - c_0)$), every
$g\in K_N$ is $\varphi_y$ for some $y\in Y^{(M)}$.

*Proof.* Write $g = \varphi_y$ ($y\in G^\natural(F_v)$). The $\Gamma(\varphi_y) = 4\operatorname{nrd}(y)^{-1}y\,\sigma(\operatorname{re}y)$
recovers $y$ up to a scalar, and $\Gamma(g)\equiv4$ (`gammaV_eq_four_add`), so $u = \Gamma(g)/4 = \operatorname{re}(u)(1+\eta_u)$ with
$\eta_u\in\mathfrak L$. The element $y^*\in Y$ with $\eta(y^*) = \eta_u$ (`exists_mem_etaY_eq`) is $\lambda y$ for a scalar $\lambda$ with
$\lambda^2\in F_v$, so $\varphi_{y^*} = \pm g$ (`phiLin_coe_mul`); in the case $-g$ the sign scalar $t$ of `exists_scalar_mul_mem`
gives $\varphi_{ty^*} = g$.

Source: Weil 1982, §3.7, pp. 64-65 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSWinIndex

open MeasureTheory Set Function Topology NumberField IsDedekindDomain WithZero
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Quat QuadFormsKB.Quat.Gnat LerayPadic

section Cover

variable {F : Type} [Field F] [NumberField F] {a b d : 𝓞 F} {K : Type} [Field K] [NumberField K] [Algebra F K]
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  {α β : 𝓞 K} (hα : (α : K) = algebraMap F K (a : F)) (hβ : (β : K) = algebraMap F K (b : F))
  (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (ha0 : (a : F) ≠ 0) (hd0 : (d : F) ≠ 0) {v : HeightOneSpectrum (𝓞 F)}
  {M : HeightOneSpectrum (𝓞 K) → ℕ} {hM1 : ∀ w, 1 ≤ M w}

local notation "Fv" => v.adicCompletion F
local notation "E" => QE (algebraMap F (v.adicCompletion F) (d : F))
local notation "Av" => algebraMap F (v.adicCompletion F) (a : F)
local notation "Bv" => algebraMap F (v.adicCompletion F) (b : F)
local notation "Dv" => algebraMap F (v.adicCompletion F) (d : F)
local notation "QF" => QuadForm.map (algebraMap (𝓞 F) F) (qNS a b d)

theorem CL.smul' {k j : ℤ} {c : Fv} (hc : Valued.v c ≤ exp (-j)) {z : E} (h : CL v k z) : CL v (j + k) (c • z) := by
  have e : exp (-(j + k)) = exp (-j) * exp (-k) := by rw [← exp_add]; congr 1; ring
  refine ⟨?_, ?_⟩
  · rw [QuadraticAlgebra.re_smul, smul_eq_mul, map_mul, e]; exact mul_le_mul' hc h.1
  · rw [QuadraticAlgebra.im_smul, smul_eq_mul, map_mul, e]; exact mul_le_mul' hc h.2

theorem QL.smul {k j : ℤ} {c : Fv} (hc : Valued.v c ≤ exp (-j)) {x : DEr Fv a b d} (h : QL v k x) :
    QL v (j + k) (c • x) :=
  ⟨h.1.smul' hc, h.2.1.smul' hc, h.2.2.1.smul' hc, h.2.2.2.smul' hc⟩

theorem QL_emb {k : ℤ} {Δ : Fin 4 → Fv} (h : ∀ i, Valued.v (Δ i) ≤ exp (-k)) : QL v k (emb Δ : DEr Fv a b d) := by
  have h0 : Valued.v (0 : Fv) ≤ exp (-k) := by rw [map_zero]; exact zero_le
  exact ⟨⟨h 0, h0⟩, ⟨h0, h 1⟩, ⟨h0, h 2⟩, ⟨h0, h 3⟩⟩

theorem QL_sum {k : ℤ} {s : Finset (Fin 4)} {f : Fin 4 → DEr Fv a b d} (h : ∀ j ∈ s, QL v k (f j)) :
    QL v k (∑ j ∈ s, f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact QL_zero k
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact (h j (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem valued_cW_le (haO : a ≠ 0) (hbO : b ≠ 0) (hdO : d ≠ 0) (j : Fin 4) :
    Valued.v (cW Av Bv Dv j) ≤ exp (-(-((eExp a haO v : ℤ) + eExp b hbO v + eExp d hdO v))) := by
  have hA := valued_eExp a haO v
  have hB := valued_eExp b hbO v
  have hD := valued_eExp d hdO v
  rw [neg_neg]
  fin_cases j
  · simp only [cW]; change Valued.v (1 : Fv) ≤ _; rw [map_one, ← exp_zero, exp_le_exp]; omega
  · change Valued.v ((Av * Dv)⁻¹) ≤ _
    rw [map_inv₀, map_mul, hA, hD, ← exp_add, ← exp_neg, exp_le_exp]; omega
  · change Valued.v ((Bv * Dv)⁻¹) ≤ _
    rw [map_inv₀, map_mul, hB, hD, ← exp_add, ← exp_neg, exp_le_exp]; omega
  · change Valued.v (-(Av * Bv * Dv)⁻¹) ≤ _
    rw [Valuation.map_neg, map_inv₀, map_mul, map_mul, hA, hB, hD, ← exp_add, ← exp_add, ← exp_neg, exp_le_exp]
    omega

include hb₀ in
/-- Coordinate level $k$ with $M_w\le e_wk$ gives membership in $\mathfrak L$. -/
theorem mem_L_of_cl {k : ℤ} (hk : ∀ w : PlaceSet (K := K) v, (M w.1 : ℤ) ≤ ramE v w.1 * k) {η : Fin 3 → E}
    (h : ∀ l, CL v k (η l)) : η ∈ LSub hb₁ α β v M := by
  intro w
  have hpl := fun l => pl_of_cl hb₀ hb₁ (h l) w
  have h2 : Valued.v (2 : w.1.adicCompletion K) ≤ 1 := by
    rw [valued_two_eq w.1, ← exp_zero, exp_le_exp]; omega
  have hA : Valued.v (algebraMap K (w.1.adicCompletion K) (α : K)) ≤ 1 := valued_algebraMap_le_one α w.1
  have hB : Valued.v (algebraMap K (w.1.adicCompletion K) (β : K)) ≤ 1 := valued_algebraMap_le_one β w.1
  have hle : ∀ l, Valued.v (qlh hb₁ v w (η l)) ≤ exp (-(M w.1 : ℤ)) := fun l =>
    (hpl l).trans (exp_le_exp.2 (by have := hk w; linarith))
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact valued_mul_le_of_le h2 (hle 0)
  · exact valued_mul_le_of_le h2 (hle 1)
  · rw [mul_assoc]; exact valued_mul_le_of_le h2 (valued_mul_le_of_le hA (hle 2))
  · rw [mul_assoc]; exact valued_mul_le_of_le h2 (valued_mul_le_of_le hB (hle 2))

theorem soSub_ext {g₁ g₂ : soSub QF Fv}
    (h : (((g₁ : orthGroup QF Fv) : GL (Fin 4) Fv) : Matrix (Fin 4) (Fin 4) Fv) =
      (((g₂ : orthGroup QF Fv) : GL (Fin 4) Fv) : Matrix (Fin 4) (Fin 4) Fv)) : g₁ = g₂ :=
  Subtype.ext (Subtype.ext (Units.ext h))

/-- The constant $e_a + e_b + e_d$ of the weights $c_j$. -/
def cGam (a b d : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) (ha0 : (a : F) ≠ 0) (hb0 : (b : F) ≠ 0) (hd0 : (d : F) ≠ 0) : ℕ :=
  eExp a (aO_ne_zero ha0) v + eExp b (aO_ne_zero hb0) v + eExp d (aO_ne_zero hd0) v

set_option maxHeartbeats 2000000 in
include hb₀ in
/-- **$K_N\subseteq U^{(M)}_v$** (every $g\in K_N$ is $\varphi_y$ with $y\in Y^{(M)}$). -/
theorem congSub_le_nsUSub (hb0 : (b : F) ≠ 0) {c₀ n N : ℕ} (hW : WinHyp hb₁ hα0 hβ0 ha0 v M c₀ n N)
    (hΓ : ∀ w : PlaceSet (K := K) v, (M w.1 : ℤ) ≤
      ramE v w.1 * ((N : ℤ) - cGam a b d v ha0 hb0 hd0 - 2 * sExp v - c₀))
    (hN : (cGam a b d v ha0 hb0 hd0 : ℤ) + 2 * sExp v < N) :
    (congSub v (qNS a b d) N (one_le_of_winHyp hb₁ hα0 hβ0 ha0 hW)).comap (soSub QF Fv).subtype ≤
      nsUSub hb₁ hα hβ ha0 hd0 v M hM1 := by
  intro g hg
  rw [Subgroup.mem_comap] at hg
  obtain ⟨y, rfl⟩ := nsSOK_surjective (K := Fv) ha0 hb0 hd0 g
  have hG : LinearMap.toMatrix' (phiLin (yv y)) ∈ ballOne v N := by
    rw [← toMatrix_nsSOK ha0 hd0]; exact hg
  set G := LinearMap.toMatrix' (phiLin (yv y))
  set x := yv y
  have h2 : (2 : Fv) ≠ 0 := two_ne_zero
  have haF : Av ≠ 0 := (map_ne_zero _).2 ha0
  have hbF : Bv ≠ 0 := (map_ne_zero _).2 hb0
  have hdF : Dv ≠ 0 := (map_ne_zero _).2 hd0
  -- `Γ(g) = 4 + S` with `S` small
  set S : DEr Fv a b d := ∑ j : Fin 4, cW Av Bv Dv j • ((emb (fun i => G i j - (1 : Matrix (Fin 4) (Fin 4) Fv) i j) :
    DEr Fv a b d) * emb (Pi.single j 1))
  have hS : QL v ((N : ℤ) - cGam a b d v ha0 hb0 hd0) S := by
    refine QL_sum fun j _ => ?_
    have h1 := ((QL_emb (k := (N : ℤ)) (a := a) (b := b) (d := d) (fun i => hG i j)).mul
      (QL_emb_single (v := v) (a := a) (b := b) (d := d) j))
    have h3 := h1.smul (valued_cW_le (aO_ne_zero ha0) (aO_ne_zero hb0) (aO_ne_zero hd0) j)
    exact h3.mono (by simp only [cGam]; push_cast; omega)
  have hΓ1 := gammaV_eq_four_add haF hbF hdF G
  have hΓ2 := gammaV_phiLin h2 haF hbF hdF x
  -- `u = Γ/4 = 1 + S/4`
  set u : DEr Fv a b d := (4 : Fv)⁻¹ • gammaV G
  have h4 : (4 : Fv) ≠ 0 := by norm_num
  have hu1 : u = 1 + (4 : Fv)⁻¹ • S := by
    simp only [u]; rw [hΓ1, smul_add, smul_smul, inv_mul_cancel₀ h4, one_smul]
  have hv4 : Valued.v ((4 : Fv)⁻¹) ≤ exp (-(-(2 * (sExp v : ℤ)))) := by
    rw [map_inv₀, show (4 : Fv) = 2 * 2 by norm_num, map_mul, valued_two_eq v, ← exp_add, ← exp_neg]
    rw [exp_le_exp]; omega
  have hS4 : QL v ((N : ℤ) - cGam a b d v ha0 hb0 hd0 - 2 * sExp v) ((4 : Fv)⁻¹ • S) :=
    (hS.smul hv4).mono (by omega)
  set k1 : ℤ := (N : ℤ) - cGam a b d v ha0 hb0 hd0 - 2 * sExp v
  have hk1 : 0 < k1 := by simp only [k1]; omega
  -- `re u` is a unit at every place
  have hre : u.re = 1 + ((4 : Fv)⁻¹ • S).re := by rw [hu1]; rfl
  have hreW : ∀ w : PlaceSet (K := K) v, Valued.v (qlh hb₁ v w u.re) = 1 := by
    intro w
    have hsmall : Valued.v (qlh hb₁ v w ((4 : Fv)⁻¹ • S).re) < 1 := by
      refine (pl_of_cl hb₀ hb₁ hS4.1 w).trans_lt ?_
      rw [← exp_zero, exp_lt_exp]
      have : (1 : ℤ) ≤ ramE v w.1 := by exact_mod_cast one_le_ramE v w.1 w.2
      nlinarith
    rw [hre, map_add, map_one]
    have := Valuation.map_add_eq_of_lt_left (Valued.v) (x := 1) (y := qlh hb₁ v w ((4 : Fv)⁻¹ • S).re)
      (by rwa [map_one])
    rwa [map_one] at this
  have hreU : IsUnit u.re := isUnit_of_qlh_ne_zero hb₀ hb₁ fun w h0 => by
    have := hreW w; rw [h0, map_zero] at this; exact zero_ne_one this
  set ηu := etaY u
  have himu : imvE u = imvE ((4 : Fv)⁻¹ • S) := by
    rw [hu1]; funext l; fin_cases l <;> simp [imvE]
  have hinvcl : CL v (0 - c₀) (Ring.inverse u.re) := hW.pl_cl _ _ (pl_zero_of_valued hb₁ _ fun w => by
    have := congrArg Valued.v (qlh_ring_inverse hb₁ hreU w)
    rw [this, map_inv₀, hreW w, inv_one])
  have hηcl : ∀ l, CL v (k1 - c₀) (ηu l) := by
    intro l
    change CL v (k1 - c₀) (Ring.inverse u.re * imvE u l)
    rw [himu]
    have hc : CL v k1 (imvE ((4 : Fv)⁻¹ • S) l) := by
      fin_cases l
      · exact hS4.2.1
      · exact hS4.2.2.1
      · exact hS4.2.2.2
    exact (hinvcl.mul hc).mono (by omega)
  have hηL : ηu ∈ LSub hb₁ α β v M := mem_L_of_cl hb₀ hb₁ (k := k1 - c₀) (fun w => hΓ w) hηcl
  obtain ⟨ys, hys, hes⟩ := exists_mem_etaY_eq hb₀ hb₁ hα hβ hα0 hβ0 (hM1 := hM1) hW.deep hW.pl_cl hW.Mn
    (by have := hW.ns; omega) hηL
  -- `y* = λ y` for a scalar `λ`
  set n₀ := nrdK x
  have hn0 : n₀ ≠ 0 := nrdK_ne_zero y.2
  have hu2 : u = ((algebraMap Fv E n₀⁻¹ * star x.re : E) : DEr Fv a b d) * x := by
    simp only [u]
    rw [hΓ2, smul_smul, show (4 : Fv)⁻¹ * (4 * n₀⁻¹) = n₀⁻¹ by field_simp, QuaternionAlgebra.coe_mul,
      ← QuaternionAlgebra.coe_commutes (star x.re) x, mul_assoc, coe_algebraMap_mul]
  have hu3 : u = (u.re : DEr Fv a b d) * (1 + pureE ηu) := coe_mul_one_add u (Ring.mul_inverse_cancel _ hreU)
  have hys' : yv ys = ((yv ys).re : DEr Fv a b d) * (1 + pureE ηu) := by
    have := yv_eq hb₀ hb₁ hα hβ hα0 hβ0 hW.deep hys; rwa [hes] at this
  set lam : E := (yv ys).re * Ring.inverse u.re * (algebraMap Fv E n₀⁻¹ * star x.re)
  have hu3' : (((yv ys).re * Ring.inverse u.re : E) : DEr Fv a b d) * u =
      ((yv ys).re : DEr Fv a b d) * (1 + pureE ηu) := by
    calc (((yv ys).re * Ring.inverse u.re : E) : DEr Fv a b d) * u =
        (((yv ys).re * Ring.inverse u.re : E) : DEr Fv a b d) * ((u.re : DEr Fv a b d) * (1 + pureE ηu)) := by
          rw [← hu3]
      _ = (((yv ys).re * Ring.inverse u.re * u.re : E) : DEr Fv a b d) * (1 + pureE ηu) := by
          rw [QuaternionAlgebra.coe_mul (_ * _) u.re, mul_assoc]
      _ = _ := by rw [mul_assoc ((yv ys).re), Ring.inverse_mul_cancel _ hreU, mul_one]
  have hlam : yv ys = (lam : DEr Fv a b d) * x := by
    calc yv ys = ((yv ys).re : DEr Fv a b d) * (1 + pureE ηu) := hys'
      _ = (((yv ys).re * Ring.inverse u.re : E) : DEr Fv a b d) * u := hu3'.symm
      _ = (((yv ys).re * Ring.inverse u.re : E) : DEr Fv a b d) *
          (((algebraMap Fv E n₀⁻¹ * star x.re : E) : DEr Fv a b d) * x) :=
        congrArg (fun z => (((yv ys).re * Ring.inverse u.re : E) : DEr Fv a b d) * z) hu2
      _ = (lam : DEr Fv a b d) * x := by rw [← mul_assoc, ← QuaternionAlgebra.coe_mul]
  -- `λ² ∈ F_v`
  set m := nrdK (yv ys) / n₀
  have hlam2 : lam ^ 2 = algebraMap Fv E m := by
    have h1 := congrArg nrdE hlam
    rw [nrdE_mul, nrdE_coe, nrdE_eq_nrdK ys.2, nrdE_eq_nrdK y.2] at h1
    have h2 : lam ^ 2 * algebraMap Fv E n₀ * algebraMap Fv E n₀⁻¹ =
        algebraMap Fv E (nrdK (yv ys)) * algebraMap Fv E n₀⁻¹ := by rw [h1]
    rw [mul_assoc, ← map_mul, mul_inv_cancel₀ hn0, map_one, mul_one, ← map_mul] at h2
    rw [show m = nrdK (yv ys) * n₀⁻¹ from div_eq_mul_inv _ _]; exact h2
  have hlam2im : (lam ^ 2).im = 0 := by rw [hlam2]; rfl
  have hphi := phiLin_coe_mul lam x hlam2im
  rw [← hlam, hlam2, QuadraticAlgebra.algebraMap_re] at hphi
  set f := m⁻¹ * QuadraticAlgebra.norm lam
  have hm0 : m ≠ 0 := div_ne_zero (nrdK_ne_zero ys.2) hn0
  have hf : f * f = 1 := by
    have h1 : QuadraticAlgebra.norm lam ^ 2 = m ^ 2 := by
      rw [← map_pow, hlam2, QuadraticAlgebra.norm_algebraMap]
    simp only [f]; field_simp; linear_combination h1
  have hmat : LinearMap.toMatrix' (phiLin (yv ys)) = f • G := by
    rw [hphi, map_smul]
  rw [nsUSub, Subgroup.mem_map]
  rcases mul_self_eq_one_iff.1 hf with h1 | h1
  · -- `φ_{y*} = g`
    refine ⟨ys, hys, soSub_ext ?_⟩
    rw [toMatrix_nsSOK, toMatrix_nsSOK, hmat, h1, one_smul]
  · -- `φ_{y*} = -g`: correct the sign with the scalar `t`
    obtain ⟨hent, hQ, -, hρ1, -⟩ := phi_entries hb₀ hb₁ hα hβ hα0 hβ0 ha0 (hM1 := hM1) hW hys
    have hk : (N : ℤ) ≤ 2 * ((n : ℤ) - c₀) := by have := hW.win; omega
    have hmG : ∀ i j, LinearMap.toMatrix' (phiLin (yv ys)) i j = -G i j := by
      intro i j; rw [hmat, h1]; simp
    have hρ' : Valued.v (-rhoY (yv ys)) = 1 := by rw [Valuation.map_neg]; exact hρ1
    have hD0 : Dco (a := Av) (b := Bv) (d := Dv) (etaY (yv ys)) 0 0 = 0 := by simp [Dco]
    have hK1 := win_K1 hk hρ' hQ hD0 (fun i j => by
      have := hG i j
      rw [show -rhoY (yv ys) * ((1 : Matrix (Fin 4) (Fin 4) Fv) i j +
          Dco (a := Av) (b := Bv) (d := Dv) (etaY (yv ys)) i j +
          coords (Qmap (etaY (yv ys)) (emb (Pi.single j 1) : DEr Fv a b d)) i) = G i j by
        rw [neg_mul, ← hent, hmG, neg_neg]]
      exact this)
    have hηw : etaY (yv ys) ∈ LwinSub a b d v N := (dco_le_iff N _).1 hK1.2
    have hρm : Valued.v (rhoY (yv ys) + 1) ≤ exp (-(N : ℤ)) := by
      rw [show rhoY (yv ys) + 1 = -(-rhoY (yv ys) - 1) by ring, Valuation.map_neg]; exact hK1.1
    obtain ⟨t, htY, -, -, htm⟩ := exists_scalar_mul_mem hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 hW hys hηw hρm
    refine ⟨t * ys, (nsLocSub hb₁ hα hβ v M hM1).mul_mem htY hys, soSub_ext ?_⟩
    rw [toMatrix_nsSOK, toMatrix_nsSOK, htm, hmat, h1, neg_one_smul, neg_neg]

end Cover

end QuadFormsKB.Tamagawa.Measure.Weil
