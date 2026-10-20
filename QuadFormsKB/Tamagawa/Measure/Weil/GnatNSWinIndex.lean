/-
# The window homomorphism and the index $[Y^{(M)} : Z_N]$

**Layer:** as in `GnatNSWinGroup`: a number field $F$, $K = F(\delta)$, a finite place $v$ of $F$ (any), $Y = Y^{(M)}$
(`nsLocSub`) at levels $M_w$, $Z_N = \{y\in Y : \varphi_y\in K_N\}$, $T = \{y\in Y : y\text{ scalar}\}$.
`WinHyp` bundles the window inequalities between $M$, $n$, $N$ and the constant $c_0$ of `exists_pl_cl`.

* **`phi_entries`**: $\varphi_y = \rho(y)\,(1 + D_{\eta(y)} + Q_{\eta(y)})$ with $|\rho(y)| = 1$, $\rho(y)\equiv\pm1\bmod\mathfrak p^N$.
* **`mem_Z_iff`**: $y\in Z_N$ iff $\eta(y)\in\mathfrak L_N$ and $\rho(y)\equiv1\bmod\mathfrak p^N$.
* **`psiY`**: $y\mapsto\eta(y)\bmod\mathfrak L_N$, a surjective homomorphism $Y\to\mathfrak L/\mathfrak L_N$ (`psiY_surjective`).
* **`ker_psiY`**: $\ker\psi = Z_N\sqcup T$ (the scalar $t = \operatorname{im}(\operatorname{re}y)\,\delta$ corrects the sign of $\rho$).
* **`index_Z`**: $[Y : Z_N] = [\mathfrak L : \mathfrak L_N]\cdot[T : T\cap Z_N]$.

Source: Weil 1982, §2.2-2.3, §3.7 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSWinGroup

open MeasureTheory Set Function Topology NumberField IsDedekindDomain WithZero
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Quat QuadFormsKB.Quat.Gnat LerayPadic

section Central

/-- **Index of $H$ in $TH$ for central $T$**: $[TH : H] = [T : T\cap H]$. -/
theorem relIndex_sup_of_central {G : Type*} [Group G] (H T : Subgroup G) (hT : ∀ t ∈ T, ∀ g : G, g * t = t * g) :
    H.relIndex (T ⊔ H) = H.relIndex T := by
  have hN : (H.subgroupOf (T ⊔ H)).Normal := by
    refine Subgroup.normal_subgroupOf_sup_of_le_normalizer fun t ht => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [← hT t ht h, mul_assoc, mul_inv_cancel, mul_one]
  have := Subgroup.relIndex_sup_right (H := T.subgroupOf (T ⊔ H)) (K := H.subgroupOf (T ⊔ H))
  rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self, Subgroup.relIndex_top_right,
    Subgroup.relIndex_subgroupOf le_sup_left] at this
  exact this

end Central

section Index

variable {F : Type} [Field F] [NumberField F] {a b d : 𝓞 F} {K : Type} [Field K] [NumberField K] [Algebra F K]
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  {α β : 𝓞 K} (hα : (α : K) = algebraMap F K (a : F)) (hβ : (β : K) = algebraMap F K (b : F))
  (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (ha0 : (a : F) ≠ 0) (hd0 : (d : F) ≠ 0) (v : HeightOneSpectrum (𝓞 F))
  (M : HeightOneSpectrum (𝓞 K) → ℕ) (hM1 : ∀ w, 1 ≤ M w)

local notation "Fv" => v.adicCompletion F
local notation "E" => QE (algebraMap F (v.adicCompletion F) (d : F))
local notation "Av" => algebraMap F (v.adicCompletion F) (a : F)
local notation "Bv" => algebraMap F (v.adicCompletion F) (b : F)
local notation "QF" => QuadForm.map (algebraMap (𝓞 F) F) (qNS a b d)

theorem aO_ne_zero {a : 𝓞 F} (ha0 : (a : F) ≠ 0) : a ≠ 0 := fun h => ha0 (by rw [h]; rfl)

/-- **The window hypotheses** relating the levels $M_w$ of $Y^{(M)}$, the auxiliary level $n$, the level $N$ of $K_N$ and the
constant $c_0$ of `exists_pl_cl`. -/
structure WinHyp (c₀ n N : ℕ) : Prop where
  deep : ∀ w, nsLevK hα0 hβ0 w ≤ M w
  pl_cl : ∀ (k : ℤ) (z : E), PL hb₁ v k z → CL v (k - c₀) z
  Mn : ∀ w : PlaceSet (K := K) v, sExp w.1 + eExp α hα0 w.1 + ramE v w.1 * n ≤ M w.1
  MN : ∀ w : PlaceSet (K := K) v,
    (M w.1 : ℤ) ≤ ramE v w.1 * ((N : ℤ) - sExp v - eExp a (aO_ne_zero ha0) v)
  win : (N : ℤ) + sExp v + c₀ + 1 ≤ 2 * ((n : ℤ) - c₀) - c₀
  ns : c₀ + sExp v < n
  Ns : sExp v + c₀ < N

variable {v M hM1} {c₀ n N : ℕ}

/-- $\rho(x) = N(\operatorname{re}x)/\operatorname{nrd}x$. -/
def rhoY (x : DEr Fv a b d) : Fv := (nrdK x)⁻¹ * QuadraticAlgebra.norm x.re

theorem toMatrix_nsSOK (y : GnK Fv a b d) :
    ((((nsSOK Fv a b d ha0 hd0 y : soSub QF Fv) : orthGroup QF Fv) : GL (Fin 4) Fv) : Matrix (Fin 4) (Fin 4) Fv) =
      LinearMap.toMatrix' (phiLin (yv y)) := by
  rw [nsSOK_coe, nsGL_apply, coe_phiSO]

theorem pi_single_eq_one_apply (i j : Fin 4) : (Pi.single j (1 : Fv) : Fin 4 → Fv) i = (1 : Matrix (Fin 4) (Fin 4) Fv) i j := by
  by_cases h : i = j
  · subst h; simp
  · rw [Pi.single_eq_of_ne h, Matrix.one_apply_ne h]

include hb₀ in
/-- **The entries of $\varphi_y$ for $y\in Y^{(M)}$**: $\rho(y)(\delta_{ij} + D_{ij} + Q_{ij})$, with $|\rho(y)| = 1$, $\rho(y)\equiv\pm1$,
$|Q_{ij}|\le q^{-2k_0}$ ($k_0 = n - c_0$). -/
theorem phi_entries (hW : WinHyp hb₁ hα0 hβ0 ha0 v M c₀ n N) {y : GnK Fv a b d}
    (hy : y ∈ nsLocSub hb₁ hα hβ v M hM1) :
    (∀ i j, LinearMap.toMatrix' (phiLin (yv y)) i j = rhoY (yv y) * ((1 : Matrix (Fin 4) (Fin 4) Fv) i j +
      Dco (a := Av) (b := Bv) (d := algebraMap F Fv (d : F)) (etaY (yv y)) i j +
      coords (Qmap (etaY (yv y)) (emb (Pi.single j 1) : DEr Fv a b d)) i)) ∧
    (∀ i j, Valued.v (coords (Qmap (etaY (yv y)) (emb (Pi.single j 1) : DEr Fv a b d)) i) ≤
      exp (-(2 * ((n : ℤ) - c₀)))) ∧
    (∀ l, CL v ((n : ℤ) - c₀) (etaY (yv y) l)) ∧
    Valued.v (rhoY (yv y)) = 1 ∧
    (Valued.v (rhoY (yv y) - 1) ≤ exp (-(N : ℤ)) ∨ Valued.v (rhoY (yv y) + 1) ≤ exp (-(N : ℤ))) := by
  have hyr := yv_eq hb₀ hb₁ hα hβ hα0 hβ0 hW.deep hy
  have hk : ∀ l, CL v ((n : ℤ) - c₀) (etaY (yv y) l) :=
    cl_of_mem_L hb₀ hb₁ hα0 hW.pl_cl hW.Mn (etaY_mem_L hb₀ hb₁ hα hβ hα0 hβ0 hW.deep hy)
  have hn0 : (0 : ℤ) ≤ (n : ℤ) - c₀ := by have := hW.ns; omega
  -- the norm `N(1+z)` is close to `1`
  set z := nrdE (pureE (etaY (yv y)) : DEr Fv a b d)
  have hz : CL v (2 * ((n : ℤ) - c₀)) z := by
    have hQ := (QL_pureE (v := v) (a := a) (b := b) hk).mul (QL_pureE hk).neg
    rw [← star_pureE] at hQ
    rw [show z = _ from nrdE_eq_re_mul_star _]
    exact hQ.1.mono (by omega)
  have hc := valued_norm_one_add_sub_one (by omega) hz
  have hρsq := rho_sq_mul_norm y.2 hyr
  have hρ1 : Valued.v (rhoY (yv y)) = 1 := by
    have hc1 : Valued.v (QuadraticAlgebra.norm (1 + z)) = 1 := by
      have h1 : Valued.v (QuadraticAlgebra.norm (1 + z) - 1) < 1 := hc.trans_lt (by
        rw [← exp_zero, exp_lt_exp]; have := hW.ns; omega)
      have := Valuation.map_add_eq_of_lt_left (Valued.v) (x := 1) (y := QuadraticAlgebra.norm (1 + z) - 1)
        (by rwa [map_one])
      rwa [add_sub_cancel, map_one] at this
    have h2 : Valued.v (rhoY (yv y)) ^ 2 = 1 := by
      have := congrArg Valued.v hρsq
      rw [map_mul, map_pow, hc1, mul_one, map_one] at this; exact this
    have hne : rhoY (yv y) ≠ 0 := by intro h0; rw [h0, map_zero] at h2; norm_num at h2
    obtain ⟨k, hk'⟩ := QuadFormsKB.Lattices.exists_valued_eq_exp v hne
    rw [hk', ← exp_nsmul, ← exp_zero, exp_inj] at h2
    rw [hk', ← exp_zero, exp_inj]; simp at h2; omega
  refine ⟨fun i j => ?_, fun i j => valued_coords_Qmap_le hk i j, hk, hρ1, ?_⟩
  · rw [toMatrix_phiLin_eq hyr, pi_single_eq_one_apply]; rfl
  · have := rho_cases (valued_two_eq v) hc (by have := hW.ns; omega) hρsq
    have hle : exp (-(2 * ((n : ℤ) - c₀) - sExp v)) ≤ exp (-(N : ℤ)) := exp_le_exp.2 (by have := hW.win; omega)
    rcases this with h | h
    · exact Or.inl (h.trans hle)
    · exact Or.inr (h.trans hle)

theorem one_le_of_winHyp (hW : WinHyp hb₁ hα0 hβ0 ha0 v M c₀ n N) : 1 ≤ N := by have := hW.Ns; omega

include hb₀ in
/-- **$y\in Z_N$ iff $\eta(y)\in\mathfrak L_N$ and $\rho(y)\equiv1\bmod\mathfrak p^N$.** -/
theorem mem_congSub_iff (hW : WinHyp hb₁ hα0 hβ0 ha0 v M c₀ n N) {y : GnK Fv a b d}
    (hy : y ∈ nsLocSub hb₁ hα hβ v M hM1) :
    ((nsSOK Fv a b d ha0 hd0 y : soSub QF Fv) : orthGroup QF Fv) ∈
        congSub v (qNS a b d) N (one_le_of_winHyp hb₁ hα0 hβ0 ha0 hW) ↔
      etaY (yv y) ∈ LwinSub a b d v N ∧ Valued.v (rhoY (yv y) - 1) ≤ exp (-(N : ℤ)) := by
  obtain ⟨hent, hQ, -, hρ1, -⟩ := phi_entries hb₀ hb₁ hα hβ hα0 hβ0 ha0 (hM1 := hM1) hW hy
  have hk : (N : ℤ) ≤ 2 * ((n : ℤ) - c₀) := by have := hW.win; omega
  rw [mem_congSub, toMatrix_nsSOK]
  constructor
  · intro hM
    have hD0 : Dco (a := Av) (b := Bv) (d := algebraMap F Fv (d : F)) (etaY (yv y)) 0 0 = 0 := by simp [Dco]
    have h := win_K1 hk hρ1 hQ hD0 (fun i j => by rw [← hent]; exact hM i j)
    exact ⟨(dco_le_iff N _).1 h.2, h.1⟩
  · rintro ⟨hη, hρ⟩ i j
    rw [hent]
    exact win_K2 hk hρ1.le hQ hρ ((dco_le_iff N _).2 hη) i j

/-! ### The sign of $\rho$ and the scalar $t = \operatorname{im}(\operatorname{re}y)\,\delta$ -/

theorem sq_delta (c : Fv) : (⟨0, c⟩ : E) ^ 2 = algebraMap Fv E (algebraMap F Fv (d : F) * c ^ 2) := by
  ext <;> simp [pow_two] <;> ring

theorem norm_delta (c : Fv) : QuadraticAlgebra.norm (⟨0, c⟩ : E) = -(algebraMap F Fv (d : F) * c ^ 2) := by
  rw [QuadraticAlgebra.norm_def]; simp; ring

theorem add_star_eq (r : E) : r + star r = algebraMap Fv E (2 * r.re) := by
  rw [← QuadraticAlgebra.algebraMap_trace_eq_add_star, QuadraticAlgebra.trace_def, zero_mul, add_zero]

theorem re_algebraMap_mul' (c : Fv) (z : E) : (algebraMap Fv E c * z).re = c * z.re := by simp

set_option maxHeartbeats 1000000 in
include hb₀ in
/-- **The sign correction**: if $\eta(y)\in\mathfrak L_N$ and $\rho(y)\equiv-1$, the scalar $t = \operatorname{im}(\operatorname{re}y)\delta$
lies in $Y^{(M)}$, is central, and $ty\in Z_N$. -/
theorem exists_scalar_mul_mem (hW : WinHyp hb₁ hα0 hβ0 ha0 v M c₀ n N) {y : GnK Fv a b d}
    (hy : y ∈ nsLocSub hb₁ hα hβ v M hM1) (hη : etaY (yv y) ∈ LwinSub a b d v N)
    (hρ : Valued.v (rhoY (yv y) + 1) ≤ exp (-(N : ℤ))) :
    ∃ t : GnK Fv a b d, t ∈ nsLocSub hb₁ hα hβ v M hM1 ∧ imvE (yv t) = 0 ∧
      ((nsSOK Fv a b d ha0 hd0 (t * y) : soSub QF Fv) : orthGroup QF Fv) ∈
        congSub v (qNS a b d) N (one_le_of_winHyp hb₁ hα0 hβ0 ha0 hW) ∧
      LinearMap.toMatrix' (phiLin (yv (t * y))) = -LinearMap.toMatrix' (phiLin (yv y)) := by
  obtain ⟨-, -, hk, hρ1, -⟩ := phi_entries hb₀ hb₁ hα hβ hα0 hβ0 ha0 (hM1 := hM1) hW hy
  have hyr := yv_eq hb₀ hb₁ hα hβ hα0 hβ0 hW.deep hy
  set r := (yv y).re with hr
  set η := etaY (yv y)
  set ρ := rhoY (yv y)
  have hru := isUnit_re_of_mem hb₀ hb₁ hα hβ hα0 hβ0 hW.deep hy
  have hval := fun w => ((mem_nsLocSub_iff hb₁ hα hβ hα0 hβ0 v M hM1 hW.deep y).1 hy w).1
  set z := nrdE (pureE η : DEr Fv a b d)
  have hz : CL v (2 * ((n : ℤ) - c₀)) z := by
    have hQ := (QL_pureE (v := v) (a := a) (b := b) hk).mul (QL_pureE hk).neg
    rw [← star_pureE] at hQ
    rw [show z = _ from nrdE_eq_re_mul_star _]
    exact hQ.1.mono (by omega)
  -- `σ(r) = ρ r (1 + z)`
  have hnrd : algebraMap Fv E (nrdK (yv y)) = r ^ 2 * (1 + z) := by
    have := congrArg nrdE hyr
    rw [nrdE_coe_mul_one_add] at this
    rw [← nrdE_eq_nrdK y.2]; exact this
  have hn0 := nrdK_ne_zero y.2
  have hρn : ρ * nrdK (yv y) = QuadraticAlgebra.norm r := by
    simp only [ρ, rhoY]; field_simp; rfl
  have hstar : star r = algebraMap Fv E ρ * r * (1 + z) := by
    have h1 : r * star r = algebraMap Fv E ρ * (r ^ 2 * (1 + z)) := by
      rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, ← hρn, map_mul, hnrd]
    exact hru.mul_left_cancel (h1.trans (by ring))
  -- `2 re(r) = r ((1 + ρ) + ρ z)` is small
  have hsum : algebraMap Fv E (2 * r.re) = r * (algebraMap Fv E (ρ + 1) + algebraMap Fv E ρ * z) := by
    rw [← add_star_eq, hstar, map_add, map_one]; ring
  have hrcl : CL v (0 - c₀) r := hW.pl_cl _ _ (pl_zero_of_valued hb₁ r hval)
  have h2 : CL v (N : ℤ) (algebraMap Fv E (ρ + 1) + algebraMap Fv E ρ * z) := by
    refine (CL.algebraMap hρ).add ?_
    have := hz.smul (j := 0) (c := ρ) (by rw [hρ1, neg_zero, exp_zero])
    exact this.mono (by have := hW.win; omega)
  have hcl := hrcl.mul h2
  rw [← hsum] at hcl
  have hre2 : Valued.v (2 * r.re) ≤ exp (-((N : ℤ) - c₀)) := by
    have := hcl.1; rw [QuadraticAlgebra.algebraMap_re] at this
    exact this.trans (exp_le_exp.2 (by omega))
  have hre : Valued.v r.re ≤ exp (-((N : ℤ) - c₀ - sExp v)) := by
    rw [map_mul, valued_two_eq v] at hre2
    by_cases h0 : r.re = 0
    · rw [h0, map_zero]; exact zero_le
    obtain ⟨k, hk'⟩ := QuadFormsKB.Lattices.exists_valued_eq_exp v h0
    rw [hk', ← exp_add, exp_le_exp] at hre2
    rw [hk', exp_le_exp]; omega
  -- `t₀ = im(r) δ` is a unit at every place
  set t₀ : E := ⟨0, r.im⟩
  have ht₀ : t₀ = r - algebraMap Fv E r.re := by ext <;> simp [t₀]
  have ht₀w : ∀ w : PlaceSet (K := K) v, Valued.v (qlh hb₁ v w t₀) = 1 := by
    intro w
    rw [ht₀, qlh_sub, qlh_algebraMap]
    have hlt : Valued.v (localRingHom v w.1 w.2 r.re) < Valued.v (qlh hb₁ v w r) := by
      rw [hval w]
      refine (valued_localRingHom_le v w.1 w.2 hre).trans_lt ?_
      rw [← exp_zero, exp_lt_exp]
      have := one_le_ramE v w.1 w.2
      have := hW.Ns
      have : (1 : ℤ) ≤ ramE v w.1 := by exact_mod_cast one_le_ramE v w.1 w.2
      nlinarith
    rw [Valuation.map_sub_eq_of_lt_left _ hlt, hval w]
  have him0 : r.im ≠ 0 := by
    intro h0
    obtain ⟨w, hw⟩ := exists_place_over hb₀ hb₁ v (K := K)
    have := ht₀w ⟨w, hw⟩
    have e : t₀ = 0 := by ext <;> simp [t₀, h0]
    rw [e, map_zero, map_zero] at this; exact zero_ne_one this
  have hdc : algebraMap F Fv (d : F) * r.im ^ 2 ≠ 0 :=
    mul_ne_zero ((map_ne_zero _).2 hd0) (pow_ne_zero _ him0)
  have hsq : nrdE (t₀ : DEr Fv a b d) = algebraMap Fv E (algebraMap F Fv (d : F) * r.im ^ 2) := by
    rw [nrdE_coe, sq_delta]
  set t : GnK Fv a b d := ⟨QuadFormsKB.Quat.Gnat.unitOfNrd (t₀ : DEr Fv a b d) _ hdc hsq,
    QuadFormsKB.Quat.Gnat.unitOfNrd_mem _ _ hdc hsq⟩
  have hyt : yv t = (t₀ : DEr Fv a b d) := rfl
  have himt : imvE (yv t) = 0 := by rw [hyt]; funext l; fin_cases l <;> rfl
  have htY : t ∈ nsLocSub hb₁ hα hβ v M hM1 := by
    refine (mem_nsLocSub_iff hb₁ hα hβ hα0 hβ0 v M hM1 hW.deep t).2 fun w => ⟨ht₀w w, ?_⟩
    rw [himt]
    convert latP_zero (u := w.1) (m := M w.1) using 1
    funext l; exact map_zero _
  refine ⟨t, htY, himt, ?_, ?_⟩
  rotate_left
  · have hty : yv (t * y) = (t₀ : DEr Fv a b d) * yv y := rfl
    have hsq' : (t₀ ^ 2).im = 0 := by rw [sq_delta]; rfl
    rw [hty, phiLin_coe_mul t₀ (yv y) hsq', sq_delta, norm_delta, QuadraticAlgebra.algebraMap_re,
      mul_neg, inv_mul_cancel₀ hdc]
    rw [show (-1 : Fv) • phiLin (yv y) = -phiLin (yv y) from by ext; simp, map_neg]
  have htyY : t * y ∈ nsLocSub hb₁ hα hβ v M hM1 := (nsLocSub hb₁ hα hβ v M hM1).mul_mem htY hy
  have hty : yv (t * y) = (t₀ : DEr Fv a b d) * yv y := rfl
  have ht₀u : IsUnit t₀ := by
    have h1 : t₀ * (t₀ * algebraMap Fv E (algebraMap F Fv (d : F) * r.im ^ 2)⁻¹) = 1 := by
      rw [← mul_assoc, ← pow_two, sq_delta, ← map_mul, mul_inv_cancel₀ hdc, map_one]
    exact ⟨⟨t₀, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  have heta : etaY (yv (t * y)) = η := by
    simp only [etaY, hty, re_coe_mul, imvE_coe_mul, smul_smul, η]
    rw [Ring.mul_inverse_rev, mul_assoc, Ring.inverse_mul_cancel _ ht₀u, mul_one]
  have hrho : rhoY (yv (t * y)) = -ρ := by
    simp only [rhoY, hty, re_coe_mul, map_mul, ρ]
    have hnt : nrdK ((t : DEK Fv a b d) * (y : DEK Fv a b d) : DEr Fv a b d) =
        (algebraMap F Fv (d : F) * r.im ^ 2) * nrdK (yv y) := by
      rw [← Units.val_mul, nrdK_mul t.2]
      show nrdK (yv t) * nrdK (yv y) = _
      rw [hyt, nrdK_of_nrdE hsq]
    change (nrdK ((t : DEK Fv a b d) * (y : DEK Fv a b d) : DEr Fv a b d))⁻¹ * _ = _
    rw [hnt, norm_delta]
    have hd' : algebraMap F Fv (d : F) ≠ 0 := (map_ne_zero _).2 hd0
    field_simp
  refine (mem_congSub_iff hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 hW htyY).2 ⟨by rw [heta]; exact hη, ?_⟩
  rw [hrho, show -ρ - 1 = -(ρ + 1) by ring, Valuation.map_neg]; exact hρ

/-! ### The subgroups $Z_N$, $T$ and the window homomorphism -/

variable (v M hM1) in
/-- **$Z_N = \{y\in Y^{(M)} : \varphi_y\in K_N\}$.** -/
def ZN (hN : 1 ≤ N) : Subgroup (nsLocSub hb₁ hα hβ v M hM1) :=
  (congSub v (qNS a b d) N hN).comap
    ((soSub QF Fv).subtype.comp ((nsSOK Fv a b d ha0 hd0).comp (nsLocSub hb₁ hα hβ v M hM1).subtype))

theorem mem_ZN_iff (hN : 1 ≤ N) (y : nsLocSub hb₁ hα hβ v M hM1) :
    y ∈ ZN hb₁ hα hβ ha0 hd0 v M hM1 hN ↔
      ((nsSOK Fv a b d ha0 hd0 (y : GnK Fv a b d) : soSub QF Fv) : orthGroup QF Fv) ∈ congSub v (qNS a b d) N hN := by
  rw [ZN, Subgroup.mem_comap]; rfl

theorem imvE_mul_of_imvE_eq_zero {x y : DEr Fv a b d} (hx : imvE x = 0) : imvE (x * y) = x.re • imvE y := by
  have e : x = (x.re : DEr Fv a b d) := by
    conv_lhs => rw [eq_re_add_pureE x, hx]
    have : (pureE (0 : Fin 3 → E) : DEr Fv a b d) = 0 := by ext <;> rfl
    rw [this, add_zero]
  rw [e, imvE_coe_mul, QuaternionAlgebra.re_coe]

variable (v M hM1) in
/-- **$T = \{y\in Y^{(M)} : y\text{ scalar}\}$** (central). -/
def TY : Subgroup (nsLocSub hb₁ hα hβ v M hM1) where
  carrier := {y | imvE (yv (y : GnK Fv a b d)) = 0}
  mul_mem' {x y} hx hy := by
    change imvE (yv (x : GnK Fv a b d) * yv (y : GnK Fv a b d)) = 0
    rw [imvE_mul_of_imvE_eq_zero hx, show imvE (yv (y : GnK Fv a b d)) = 0 from hy, smul_zero]
  one_mem' := by
    change imvE (1 : DEr Fv a b d) = 0
    funext l; fin_cases l <;> rfl
  inv_mem' {x} hx := by
    set u : DEK Fv a b d := ((x : GnK Fv a b d) : DEK Fv a b d)
    change imvE ((u⁻¹ : DEK Fv a b d) : DEr Fv a b d) = 0
    have hx' : imvE (u : DEr Fv a b d) = 0 := hx
    set r := (u : DEr Fv a b d).re
    have hu : (u : DEr Fv a b d) = (r : DEr Fv a b d) := by
      conv_lhs => rw [eq_re_add_pureE (u : DEr Fv a b d), hx']
      have : (pureE (0 : Fin 3 → E) : DEr Fv a b d) = 0 := by ext <;> rfl
      rw [this, add_zero]
    have h2 : (r : DEr Fv a b d) * ((u⁻¹ : DEK Fv a b d) : DEr Fv a b d) = 1 := by
      rw [QuaternionAlgebra.coe_commutes, ← hu]; exact Units.inv_mul u
    have hr : IsUnit r := by
      have := congrArg nrdE h2
      rw [nrdE_mul, nrdE_coe, nrdE_one] at this
      refine isUnit_of_mul_isUnit_left (y := r * nrdE ((u⁻¹ : DEK Fv a b d) : DEr Fv a b d)) ?_
      rw [← mul_assoc, ← pow_two, this]; exact isUnit_one
    have h3 := congrArg imvE h2
    rw [imvE_coe_mul] at h3
    have h4 : imvE (1 : DEr Fv a b d) = 0 := by funext l; fin_cases l <;> rfl
    rw [h4] at h3
    have := congrArg (fun z => Ring.inverse r • z) h3
    simp only [smul_smul, Ring.inverse_mul_cancel r hr, one_smul, smul_zero] at this
    exact this

variable (a b α β v M) in
/-- The quotient $\mathfrak L/\mathfrak L_N$. -/
abbrev LQuot (N : ℕ) := (LSub hb₁ α β v M) ⧸ (LwinSub a b d v N).addSubgroupOf (LSub hb₁ α β v M)

theorem etaY_one : etaY (1 : DEr Fv a b d) = 0 := by
  unfold etaY
  have : imvE (1 : DEr Fv a b d) = 0 := by funext l; fin_cases l <;> rfl
  rw [this, smul_zero]

include hb₀ in
/-- **The window homomorphism** $\psi : Y^{(M)}\to\mathfrak L/\mathfrak L_N$, $y\mapsto\eta(y)$. -/
def psiY (hW : WinHyp hb₁ hα0 hβ0 ha0 v M c₀ n N) :
    nsLocSub hb₁ hα hβ v M hM1 →* Multiplicative (LQuot a b hb₁ α β v M N) where
  toFun y := Multiplicative.ofAdd (QuotientAddGroup.mk
    ⟨etaY (yv (y : GnK Fv a b d)), etaY_mem_L hb₀ hb₁ hα hβ hα0 hβ0 hW.deep y.2⟩)
  map_one' := by
    rw [← ofAdd_zero]; congr 1
    rw [← QuotientAddGroup.mk_zero]; congr 1
    exact Subtype.ext etaY_one
  map_mul' y y' := by
    rw [← ofAdd_add]
    apply congrArg Multiplicative.ofAdd
    rw [← QuotientAddGroup.mk_add, QuotientAddGroup.eq]
    have := etaY_mul_sub_mem hb₀ hb₁ hα hβ hα0 hβ0 hW.deep hW.pl_cl hW.Mn (N := N)
      (by have := hW.win; omega) (by have := hW.ns; omega) y.2 y'.2
    rw [AddSubgroup.mem_addSubgroupOf]
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
    have h := (LwinSub a b d v N).neg_mem this
    have e : -etaY (yv ((y * y' : nsLocSub hb₁ hα hβ v M hM1) : GnK Fv a b d)) +
        (etaY (yv (y : GnK Fv a b d)) + etaY (yv (y' : GnK Fv a b d))) =
        -(etaY (yv ((y : GnK Fv a b d) * (y' : GnK Fv a b d))) - etaY (yv (y : GnK Fv a b d)) -
          etaY (yv (y' : GnK Fv a b d))) := by
      change -etaY (yv ((y : GnK Fv a b d) * (y' : GnK Fv a b d))) + _ = _
      abel
    rw [e]; exact h

include hb₀ in
theorem mem_ker_psiY (hW : WinHyp hb₁ hα0 hβ0 ha0 v M c₀ n N) (y : nsLocSub hb₁ hα hβ v M hM1) :
    y ∈ (psiY hb₀ hb₁ hα hβ hα0 hβ0 ha0 (hM1 := hM1) hW).ker ↔
      etaY (yv (y : GnK Fv a b d)) ∈ LwinSub a b d v N := by
  rw [MonoidHom.mem_ker]
  change Multiplicative.ofAdd _ = 1 ↔ _
  rw [← ofAdd_zero, EmbeddingLike.apply_eq_iff_eq, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]

include hb₀ in
theorem psiY_surjective (hW : WinHyp hb₁ hα0 hβ0 ha0 v M c₀ n N) :
    Function.Surjective (psiY hb₀ hb₁ hα hβ hα0 hβ0 ha0 (hM1 := hM1) hW) := by
  intro q
  induction q using Multiplicative.rec with | ofAdd q => ?_
  induction q using QuotientAddGroup.induction_on with | H q => ?_
  obtain ⟨y, hy, he⟩ := exists_mem_etaY_eq hb₀ hb₁ hα hβ hα0 hβ0 (hM1 := hM1) hW.deep hW.pl_cl hW.Mn
    (by have := hW.ns; omega) q.2
  exact ⟨⟨y, hy⟩, congrArg (fun z => Multiplicative.ofAdd (QuotientAddGroup.mk z)) (Subtype.ext he)⟩

theorem TY_central (t : nsLocSub hb₁ hα hβ v M hM1) (ht : t ∈ TY hb₁ hα hβ v M hM1)
    (g : nsLocSub hb₁ hα hβ v M hM1) : g * t = t * g := by
  have ht' : imvE (yv (t : GnK Fv a b d)) = 0 := ht
  have hu : yv (t : GnK Fv a b d) = ((yv (t : GnK Fv a b d)).re : DEr Fv a b d) := by
    conv_lhs => rw [eq_re_add_pureE (yv (t : GnK Fv a b d)), ht']
    have : (pureE (0 : Fin 3 → E) : DEr Fv a b d) = 0 := by ext <;> rfl
    rw [this, add_zero]
  apply Subtype.ext; apply Subtype.ext; apply Units.ext
  change yv (g : GnK Fv a b d) * yv (t : GnK Fv a b d) = yv (t : GnK Fv a b d) * yv (g : GnK Fv a b d)
  rw [hu]; exact (QuaternionAlgebra.coe_commutes _ _).symm

include hb₀ in
/-- **$\ker\psi = T\,Z_N$.** -/
theorem ker_psiY (hW : WinHyp hb₁ hα0 hβ0 ha0 v M c₀ n N) :
    (psiY hb₀ hb₁ hα hβ hα0 hβ0 ha0 (hM1 := hM1) hW).ker =
      TY hb₁ hα hβ v M hM1 ⊔ ZN hb₁ hα hβ ha0 hd0 v M hM1 (one_le_of_winHyp hb₁ hα0 hβ0 ha0 hW) := by
  apply le_antisymm
  · intro y hy
    rw [mem_ker_psiY] at hy
    obtain ⟨-, -, -, -, hρ⟩ := phi_entries hb₀ hb₁ hα hβ hα0 hβ0 ha0 (hM1 := hM1) hW y.2
    rcases hρ with hρ | hρ
    · refine Subgroup.mem_sup_right ?_
      rw [mem_ZN_iff]
      exact (mem_congSub_iff hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 hW y.2).2 ⟨hy, hρ⟩
    · obtain ⟨t, htY, ht0, htK, -⟩ := exists_scalar_mul_mem hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 hW y.2 hy hρ
      have h1 : (⟨t, htY⟩ : nsLocSub hb₁ hα hβ v M hM1) ∈ TY hb₁ hα hβ v M hM1 := ht0
      have h2 : (⟨t, htY⟩ * y : nsLocSub hb₁ hα hβ v M hM1) ∈
          ZN hb₁ hα hβ ha0 hd0 v M hM1 (one_le_of_winHyp hb₁ hα0 hβ0 ha0 hW) := by
        rw [mem_ZN_iff]; exact htK
      have e : y = (⟨t, htY⟩ : nsLocSub hb₁ hα hβ v M hM1)⁻¹ * (⟨t, htY⟩ * y) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.inv_mem _ h1)) (Subgroup.mem_sup_right h2)
  · refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · rw [mem_ker_psiY]
      have : imvE (yv (y : GnK Fv a b d)) = 0 := hy
      unfold etaY; rw [this, smul_zero]; exact (LwinSub a b d v N).zero_mem
    · rw [mem_ker_psiY]
      rw [mem_ZN_iff] at hy
      exact ((mem_congSub_iff hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 hW y.2).1 hy).1

include hb₀ in
/-- **$[Y^{(M)} : Z_N] = [\mathfrak L : \mathfrak L_N]\cdot[T : T\cap Z_N]$.** -/
theorem index_ZN (hW : WinHyp hb₁ hα0 hβ0 ha0 v M c₀ n N) :
    (ZN hb₁ hα hβ ha0 hd0 v M hM1 (one_le_of_winHyp hb₁ hα0 hβ0 ha0 hW)).index =
      ((LwinSub a b d v N).addSubgroupOf (LSub hb₁ α β v M)).index *
        (ZN hb₁ hα hβ ha0 hd0 v M hM1 (one_le_of_winHyp hb₁ hα0 hβ0 ha0 hW)).relIndex (TY hb₁ hα hβ v M hM1) := by
  set Z := ZN hb₁ hα hβ ha0 hd0 v M hM1 (one_le_of_winHyp hb₁ hα0 hβ0 ha0 hW)
  set T := TY hb₁ hα hβ v M hM1
  have h1 := Subgroup.relIndex_mul_index (H := Z) (K := T ⊔ Z) le_sup_right
  rw [relIndex_sup_of_central Z T (fun t ht g => TY_central hb₁ hα hβ t ht g),
    ← ker_psiY hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 hW, Subgroup.index_ker,
    MonoidHom.range_eq_top.2 (psiY_surjective hb₀ hb₁ hα hβ hα0 hβ0 ha0 hW), Subgroup.card_top] at h1
  rw [← h1, mul_comm]
  rfl

end Index

end QuadFormsKB.Tamagawa.Measure.Weil
