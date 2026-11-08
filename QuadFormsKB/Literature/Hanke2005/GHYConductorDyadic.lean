/-
# The conductor at a dyadic ramified place; Gan–Hanke–Yu Prop. 7.5 unconditional

W. T. Gan, J. Hanke, J.-K. Yu, *On an exact mass formula of Shimura*, Duke Math. J. 107 (2001), Lemma A.1(iv), p. 123;
§6, (6.3), (6.5), (6.13); Proposition 7.5, p. 119. O. T. O'Meara, *Introduction to quadratic forms*, 91:2.

Let $v$ be a dyadic place ramified in $E_\delta = F_v(\sqrt\delta)$, and $\Lambda = \mathcal O_F^n$ maximal for $Q_0$ of even rank
$n\ge4$. Following Gan–Hanke–Yu (6.3), (6.5), (6.13), purely locally:

* $\Lambda_v\simeq\mathbb H^k\perp N$ with $N$ anisotropic and maximal (`exists_hypSum_shape`, O'Meara 91:2), and
  $[\widetilde\Lambda_v:\Lambda_v] = |\det H_N|^{-1}$;
* ramification forces $N$ binary with residue zero space of dimension $1$ (`kernel_ram_shape`): a unimodular binary
  (cross coefficient a unit) has unramified discriminant (`isUnramSqrt_binary`), which excludes the kernels $0$, $S$,
  $\pi S$ and $\pi T'\perp T$;
* then $N\simeq a(x^2 + txy + ny^2)$ is the scaled norm form of $\mathcal O_{E_\delta}$ (`ramBinary_data`, Gan–Hanke–Yu's $A_{E_\delta}$),
  $[\widetilde\Lambda_v:\Lambda_v] = q^d$ with $\pi^d\,\|\,4n - t^2$ the discriminant exponent, and the conductor exponent of
  $E_\delta$ is $d$ (`condExp_eq_disc`, from `isNorm_of_pow_dvd` and `exists_not_isNorm`: Gan–Hanke–Yu Lemma A.1(iv), $U^i\subseteq NE^\times$
  iff $i\ge d$).

Hence `RamifiedDualIndexConductorDyadic` holds (`ramifiedDualIndexConductorDyadic`), so does `RamifiedDualIndexConductor`
(`ramifiedDualIndexConductor_proved`), and **Gan–Hanke–Yu Proposition 7.5 holds with no named input** (`ghy_prop75_proved`).
-/
import QuadFormsKB.Literature.Hanke2005.GHYConductorOdd
import QuadFormsKB.Literature.Hanke2005.GHYEvenDual
import QuadFormsKB.Literature.Hanke2005.DyadicR2RamConductor

open NumberField IsDedekindDomain
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.deprecated false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil
  QuadFormsKB.Tamagawa.Indefinite QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR QuadFormsKB.Tamagawa.LatChange
  QuadFormsKB.LocalDensity.HypFrame QuadForm

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

section Local

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-! ### Unramified discriminants -/

theorem isUnramSqrt_mul {x y : Fv} (hx : IsUnramSqrt v x) (hy : IsUnramSqrt v y) : IsUnramSqrt v (x * y) := by
  obtain ⟨c, hc, a, ha, hxa⟩ := hx
  obtain ⟨c', hc', b, hb, hyb⟩ := hy
  refine ⟨c * c', mul_ne_zero hc hc', a + b + 4 * a * b, ?_, ?_⟩
  · rw [show 1 + 4 * (a + b + 4 * a * b) = (1 + 4 * a) * (1 + 4 * b) by ring]; exact ha.mul hb
  · rw [show x * y * (c * c') ^ 2 = (x * c ^ 2) * (y * c' ^ 2) by ring, hxa, hyb]
    push_cast
    rw [show ((4 : 𝔬) : Fv) = 4 from map_ofNat (algebraMap 𝔬 Fv) 4]
    ring

/-- **A unimodular binary at a dyadic place has unramified discriminant:** if the cross coefficient $b$ of $S$ is a unit,
$-\det H_S/4\cdot(2/b)^2 = 1 - 4ac/b^2$. -/
theorem isUnramSqrt_binary (h2 : ¬ IsUnit (2 : 𝔬)) (S : QuadForm 𝔬 2) (hb : IsUnit (S.coeff 0 1)) :
    IsUnramSqrt v (-(((S.hessian.det : 𝔬) : Fv)) / 4) := by
  have hπ := NF.irreducible_π v
  have h2π := pi_dvd_two_of_not_isUnit v h2
  obtain ⟨binv, hbinv⟩ := hb.exists_right_inv
  have hb0 : ((S.coeff 0 1 : 𝔬) : Fv) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).mpr hb.ne_zero
  have hbinv' : ((binv : 𝔬) : Fv) = ((S.coeff 0 1 : 𝔬) : Fv)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    have := congrArg (fun z : 𝔬 => (z : Fv)) hbinv
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at this
    rw [mul_comm]; exact this
  refine ⟨2 / ((S.coeff 0 1 : 𝔬) : Fv), div_ne_zero two_ne_zero hb0, -(S.coeff 0 0 * S.coeff 1 1 * binv ^ 2), ?_, ?_⟩
  · refine dvr_isUnit_of_not_dvd hπ fun h => hπ.not_isUnit (isUnit_of_dvd_one ?_)
    have h4 : NF.π v ∣ 4 * -(S.coeff 0 0 * S.coeff 1 1 * binv ^ 2) :=
      dvd_mul_of_dvd_left (h2π.trans ⟨2, by norm_num⟩) _
    have := dvd_sub h h4
    simpa using this
  · rw [det_hessian_binary]
    push_cast
    rw [hbinv']
    field_simp
    rw [show ((4 : 𝔬) : Fv) = 4 from map_ofNat (algebraMap 𝔬 Fv) 4]
    ring

/-- **Ramification forces the binary kernel with residue zero space of dimension $1$** (Gan–Hanke–Yu 2001, (6.3)): if the
anisotropic maximal kernel $N$ (dimension $2$ or $4$) has ramified discriminant, then $N$ is binary and not all its values
lie in $\mathfrak p$. ($N = \pi S$ and $N\simeq\pi T'\perp T$ have unramified discriminant.) -/
@[kb "ganhankeyu2001" "§6, (6.3) (E_δ ramified: the anisotropic kernel is the binary A_{E_δ})"]
theorem kernel_ram_shape (h2 : ¬ IsUnit (2 : 𝔬)) {r : ℕ} (hr : r = 2 ∨ r = 4) (N : QuadForm 𝔬 r)
    (hmax : MaxProp v (N.map (algebraMap 𝔬 Fv)))
    (han : ∀ y : Fin r → Fv, (N.map (algebraMap 𝔬 Fv)).eval y = 0 → y = 0)
    (hram : ¬ IsUnramSqrt v ((-1) ^ (r / 2) * (dN v N / 2 ^ r))) :
    r = 2 ∧ ¬ ∀ y, NF.π v ∣ N.eval y := by
  have hπ := NF.irreducible_π v
  have h2π := pi_dvd_two_of_not_isUnit v h2
  have h20 := two_ne_zero_O v
  have han' := aniso_integral v N han
  have hmax' := hmax_of_maxProp v h2 N hmax han'
  have hπ0 : ((NF.π v : 𝔬) : Fv) ≠ 0 := pi_ne_zero_Fv v
  rcases hr with rfl | rfl
  · refine ⟨rfl, fun hall => hram ?_⟩
    obtain ⟨S, hS⟩ := exists_eq_smul_of_dvd_eval hπ.ne_zero N hall
    have hSan : ∀ y : Fin 2 → 𝔬, NF.π v ∣ S.eval y → ∀ i, NF.π v ∣ y i := fun y hy i =>
      hmax' y (by rw [hS, eval_smul_form, pow_two]; exact mul_dvd_mul_left _ hy) i
    have hbu : IsUnit (S.coeff 0 1) := dvr_isUnit_of_not_dvd hπ (not_dvd_coeff01_of_aniso hπ h2π S hSan)
    have hdetN : N.hessian.det = NF.π v ^ 2 * S.hessian.det := by rw [hS, hessian_smul_det_two]
    have e : (-1 : Fv) ^ (2 / 2) * (dN v N / 2 ^ 2) =
        (-(((S.hessian.det : 𝔬) : Fv)) / 4) * ((NF.π v : 𝔬) : Fv) ^ 2 := by
      rw [dN, hdetN]; push_cast; ring
    rw [e, isUnramSqrt_mul_sq v _ _ hπ0]
    exact isUnramSqrt_binary v h2 S hbu
  · exfalso
    apply hram
    set W := resZeroSub hπ h2π h20 N han' with hW
    have hlo := le_finrank_resZeroSub_add_two hπ h2π h20 N han'
    have hhi := finrank_resZeroSub_le_two hπ h2π h20 N han' hmax'
    rw [← hW] at hlo hhi
    have hs2 : Module.finrank (IsLocalRing.ResidueField 𝔬) W = 2 := by omega
    obtain ⟨M, T, hTu, hTan, hMd, hM⟩ := exists_shape_top (m := 2) hπ h2π h20 N han' hs2
    obtain ⟨T', hT'⟩ := exists_eq_smul_of_dvd_eval hπ.ne_zero M hMd
    rw [hT'] at hM
    have hmax2 := hmax_of_isGLEquiv hM hmax'
    have hT'an : ∀ y : Fin 2 → 𝔬, NF.π v ∣ T'.eval y → ∀ i, NF.π v ∣ y i := by
      intro y hy i
      have h := hmax2 (Fin.append y 0) (by
        rw [eval_orthSum_append, eval_smul_form, pow_two]
        have h0 : T.eval (0 : Fin 2 → 𝔬) = 0 := by simp [QuadForm.eval, QuadForm.evalIn]
        rw [h0, add_zero]
        exact mul_dvd_mul_left _ hy) (Fin.castAdd 2 i)
      simpa using h
    have hbT := dvr_isUnit_of_not_dvd hπ (not_dvd_coeff01_of_aniso hπ h2π T hTan)
    have hbT' := dvr_isUnit_of_not_dvd hπ (not_dvd_coeff01_of_aniso hπ h2π T' hT'an)
    obtain ⟨u, hu, hdu⟩ := hM.det_hessian
    rw [Hanke2011Structure.hessian_orthSum_det, hessian_smul_det_two] at hdu
    have hu0 : ((u : 𝔬) : Fv) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).mpr hu.ne_zero
    have hdu' : ((u : 𝔬) : Fv) ^ 2 * dN v N =
        ((NF.π v : 𝔬) : Fv) ^ 2 * ((T'.hessian.det : 𝔬) : Fv) * ((T.hessian.det : 𝔬) : Fv) := by
      have := congrArg (fun z : 𝔬 => (z : Fv)) hdu
      push_cast at this
      rw [dN]; exact this.symm
    have hdN : dN v N = ((NF.π v : 𝔬) : Fv) ^ 2 * ((T'.hessian.det : 𝔬) : Fv) * ((T.hessian.det : 𝔬) : Fv) /
        ((u : 𝔬) : Fv) ^ 2 := by
      rw [eq_div_iff (pow_ne_zero 2 hu0), mul_comm]; exact hdu'
    have e : (-1 : Fv) ^ (4 / 2) * (dN v N / 2 ^ 4) =
        ((-(((T'.hessian.det : 𝔬) : Fv)) / 4) * (-(((T.hessian.det : 𝔬) : Fv)) / 4)) *
          (((NF.π v : 𝔬) : Fv) / ((u : 𝔬) : Fv)) ^ 2 := by
      rw [hdN]; field_simp; ring
    rw [e, isUnramSqrt_mul_sq v _ _ (div_ne_zero hπ0 hu0)]
    exact isUnramSqrt_mul v (isUnramSqrt_binary v h2 T' hbT') (isUnramSqrt_binary v h2 T hbT)

/-- **The conductor exponent of $F_v(\sqrt\delta)$ at a dyadic place is the discriminant exponent $d$** (Gan–Hanke–Yu 2001,
Lemma A.1(iv), p. 123: $U^i\subseteq NE^\times$ iff $i\ge d$): for $\delta = (t^2 - 4n)/4$ up to squares, $\pi\mid t$, $\pi\,\|\,n$,
$\pi^d\,\|\,4n - t^2$. -/
@[kb "ganhankeyu2001" "Lemma A.1(iv), p. 123 (f = d at a ramified dyadic place)"]
theorem condExp_eq_disc (h2 : ¬ IsUnit (2 : 𝔬)) {t nn w : 𝔬} (ht : NF.π v ∣ t) (hn : nn = NF.π v * w)
    (hw : IsUnit w) {d : ℕ} (hd : NF.π v ^ d ∣ 4 * nn - t ^ 2) (hd' : ¬ NF.π v ^ (d + 1) ∣ 4 * nn - t ^ 2)
    {x c : Fv} (hc : c ≠ 0) (hx : x = R2Ram.delta (K := Fv) t nn * c ^ 2) : condExp v x = d := by
  classical
  have hπ := NF.irreducible_π v
  have h2π := pi_dvd_two_of_not_isUnit v h2
  have h20 := two_ne_zero_O v
  obtain ⟨e, he, he'⟩ := exists_pow_dvd_not_dvd (NF.π v) hπ h20
  obtain ⟨v2, hv2, hv2u⟩ := dvr_exact hπ he he'
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · subst h0; exact absurd (by simpa using h2π) he'
    · exact h0
  have hsq : ∀ y : 𝔬, NF.π v ^ (2 * e + 1) ∣ y - 1 → IsSquare y := fun y hy =>
    isSquare_of_pow_dvd_sub_one hπ h2π h20 hv2u hv2 hy
  have h2K : (2 : Fv) ≠ 0 := two_ne_zero
  have key : ∀ u : 𝔬, IsUnit u → (hilbertSymbol Fv x (u : Fv) = 1 ↔ ∃ a b, R2Ram.nrm t nn a b = u) := by
    intro u hu
    rw [hx, HM3.hilbertSymbol_mul_sq_left _ _ _ _ hc, hilbertSymbol_comm]
    exact (R2Ram.isNorm_iff_hilbert (K := Fv) hπ ht hn hw h2K hu.ne_zero).symm
  have P : ∀ m : ℕ, (∀ u : 𝔬, IsUnit u → NF.π v ^ m ∣ u - 1 → hilbertSymbol Fv x (u : Fv) = 1) ↔ d ≤ m := by
    intro m
    constructor
    · intro hm
      by_contra hlt
      obtain ⟨u, hu, hud, hnu⟩ := R2Ram.exists_not_isNorm hπ ht hn hw hv2u hv2 he1 hd hd'
      exact hnu ((key u hu).1 (hm u hu ((pow_dvd_pow _ (by omega)).trans hud)))
    · intro hdm u hu hum
      exact (key u hu).2
        (R2Ram.isNorm_of_pow_dvd hπ ht hn hw hv2u hv2 hsq hd hd' hu ((pow_dvd_pow _ hdm).trans hum))
  have hex : ∃ c : ℕ, ∀ u : 𝔬, IsUnit u → NF.π v ^ c ∣ u - 1 → hilbertSymbol Fv x (u : Fv) = 1 :=
    ⟨d, (P d).2 le_rfl⟩
  unfold condExp
  rw [dif_pos hex, Nat.find_eq_iff]
  exact ⟨(P d).2 le_rfl, fun m hm h => absurd ((P m).1 h) (by omega)⟩

/-- **The dual index at a ramified dyadic place is the norm of the conductor** (Gan–Hanke–Yu 2001, Lemma A.1(iv), (6.5), (6.13)):
for even $n\ge4$, $\mathcal O_F^n$ maximal and $v$ dyadic and ramified in $F_v(\sqrt\delta)$,
$[\widetilde\Lambda_v:\Lambda_v] = q_v^{f_v}$. -/
@[kb "ganhankeyu2001" "Lemma A.1(iv), p. 123; (6.5), (6.13) (dual index at a ramified dyadic place)"]
theorem dualIndexAt_ram_dyadic (hn : 4 ≤ n) (heven : Even n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (hmax : StdIsMaximal Q₀) (h2 : ¬ IsUnit (2 : 𝔬)) (hr : IsRamifiedAt v Q₀) :
    dualIndexAt v Q₀ = (normQ v) ^ condExp v (algebraMap F Fv (discK Q₀)) := by
  obtain ⟨k, r, h, N, hN, hNM, hNa, hE⟩ :=
    exists_hypSum_shape v n (NF.Qp v Q₀) (NF.nondegenerate_Qp v hQ) (maxProp_Qp v Q₀ hQ hmax)
  subst h
  have hr4 : r ≤ 4 := rank_le_four_of_aniso v _ hNa
  have hreven : Even r := by
    obtain ⟨j, hj⟩ := heven
    exact ⟨j - k, by omega⟩
  obtain ⟨U, hU, hUe⟩ := hE
  set DQ := (NF.Qp v Q₀).hessian.det with hDQ
  set DH := (hypSum N k).hessian.det with hDH
  have hHess := DVR.hessian_eq_of_eval hUe
  have hDHeq : DH = U.det * U.det * DQ := by
    rw [hDH, hHess, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    ring
  have hcoe : ((DH : 𝔬) : Fv) = ((U.det : 𝔬) : Fv) ^ 2 * ((DQ : 𝔬) : Fv) := by
    rw [hDHeq]; push_cast; ring
  have hnormU := norm_coe_unit v hU
  have hnormDH : ‖((DH : 𝔬) : Fv)‖ = ‖((DQ : 𝔬) : Fv)‖ := by
    rw [hcoe, norm_mul, norm_pow, hnormU, one_pow, one_mul]
  have hdual : dualIndexAt v Q₀ = ‖dN v N‖⁻¹ := by
    unfold dualIndexAt
    rw [← hDQ, ← hnormDH, hDH, norm_det_hypSum]
  have key : algebraMap F (v.adicCompletion F) ((Q₀.map (algebraMap (𝓞 F) F)).hessian.det) =
      ((DQ : 𝔬) : Fv) := by
    rw [hDQ, hessian_det_cast v Q₀]
    have : (Q₀.map (algebraMap (𝓞 F) F)).hessian = Q₀.hessian.map (algebraMap (𝓞 F) F) := by
      ext i j; simp [QuadForm.hessian, QuadForm.map]
    rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rfl
  have hdisc : algebraMap F (v.adicCompletion F) (discK Q₀) =
      (-1) ^ ((r + 2 * k) / 2) * (((DQ : 𝔬) : Fv) / 2 ^ (r + 2 * k)) := by
    unfold discK
    rw [map_mul, map_div₀, map_pow, map_pow, map_neg, map_one, map_ofNat, key]
  have hramiff : IsRamifiedAt v Q₀ ↔ ¬ IsUnramSqrt v ((-1) ^ (r / 2) * (dN v N / 2 ^ r)) := by
    rw [← ram_hypSum v N k]
    unfold IsRamifiedAt
    rw [hdisc, ← hDH, hcoe]
    refine not_congr ?_
    have : (-1 : Fv) ^ ((r + 2 * k) / 2) *
        (((U.det : 𝔬) : Fv) ^ 2 * ((DQ : 𝔬) : Fv) / 2 ^ (r + 2 * k)) =
        ((-1) ^ ((r + 2 * k) / 2) * (((DQ : 𝔬) : Fv) / 2 ^ (r + 2 * k))) * ((U.det : 𝔬) : Fv) ^ 2 := by ring
    rw [this]
    exact (isUnramSqrt_mul_unit_sq v _ _ hU).symm
  have hramN := hramiff.1 hr
  have hD : ‖dN v N‖⁻¹ ≠ 1 := fun h1 => not_isRamifiedAt_of_dualIndexAt_eq_one v Q₀ heven (hdual.trans h1) hr
  have hr24 : r = 2 ∨ r = 4 := by
    obtain ⟨j, hj⟩ := hreven
    rcases (show r = 0 ∨ r = 2 ∨ r = 4 by omega) with h0 | h | h
    · subst h0; exact absurd (by simp [dN]) hD
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨rfl, hnot⟩ := kernel_ram_shape v h2 hr24 N hNM hNa hramN
  obtain ⟨a, t, nn, w, g, d, hau, ht, hnn, hw, hGL, hdetN, hgu, hd, hd', hd1⟩ :=
    R2Ram.ramBinary_data v h2 N hN hNM hNa hD hnot
  -- the dual index is `q^d`
  obtain ⟨ε, hε, hεu⟩ := dvr_exact (NF.irreducible_π v) hd hd'
  have hdet' : N.hessian.det = NF.π v ^ d * (g ^ 2 * ε) := by rw [hdetN, hε]; ring
  have hdualq : dualIndexAt v Q₀ = normQ v ^ d := by
    rw [hdual, dN, hdet', norm_pi_pow_mul_unit v d ((hgu.pow 2).mul hεu), inv_inv, DensitySD.q_eq]
  -- the discriminant is `δ · c²`
  have hUd0 : ((U.det : 𝔬) : Fv) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).mpr hU.ne_zero
  have hg0 : ((g : 𝔬) : Fv) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).mpr hgu.ne_zero
  have h2F : (2 : Fv) ≠ 0 := two_ne_zero
  have hDHv : ((DH : 𝔬) : Fv) =
      (-1) ^ k * (((g : 𝔬) : Fv) ^ 2 * (4 * ((nn : 𝔬) : Fv) - ((t : 𝔬) : Fv) ^ 2)) := by
    rw [hDH, det_hypSum_coe, dN, hdetN]; push_cast; rfl
  have hDQv : ((DQ : 𝔬) : Fv) =
      (-1) ^ k * (((g : 𝔬) : Fv) ^ 2 * (4 * ((nn : 𝔬) : Fv) - ((t : 𝔬) : Fv) ^ 2)) / ((U.det : 𝔬) : Fv) ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hUd0), ← hDHv, hcoe, mul_comm]
  have hm : ((-1 : Fv) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  have hx : algebraMap F Fv (discK Q₀) = R2Ram.delta (K := Fv) t nn *
      (((g : 𝔬) : Fv) / (2 ^ k * ((U.det : 𝔬) : Fv))) ^ 2 := by
    rw [hdisc, hDQv, R2Ram.delta, show (2 + 2 * k) / 2 = k + 1 by omega, pow_succ]
    simp only [show ∀ z : 𝔬, algebraMap 𝔬 Fv z = (z : Fv) from fun _ => rfl]
    linear_combination (-(((g : 𝔬) : Fv) ^ 2 * (4 * ((nn : 𝔬) : Fv) - ((t : 𝔬) : Fv) ^ 2)) /
      (((U.det : 𝔬) : Fv) ^ 2 * 2 ^ (2 + 2 * k))) * hm
  rw [hdualq, condExp_eq_disc v h2 ht hnn hw hd hd'
    (div_ne_zero hg0 (mul_ne_zero (pow_ne_zero _ h2F) hUd0)) hx]

end Local

/-- **`RamifiedDualIndexConductorDyadic` is proved** (Gan–Hanke–Yu 2001, Lemma A.1(iv), (6.5), (6.13); `dualIndexAt_ram_dyadic`). -/
@[kb "ganhankeyu2001" "Lemma A.1(iv), p. 123; (6.5), (6.13) (dyadic places)"]
theorem ramifiedDualIndexConductorDyadic : RamifiedDualIndexConductorDyadic F :=
  ⟨fun hn heven Q₀ hQ hmax v h2 hr => dualIndexAt_ram_dyadic v hn heven Q₀ hQ hmax h2 hr⟩

/-- **`RamifiedDualIndexConductor` is proved** at every place. -/
@[kb "ganhankeyu2001" "Lemma A.1(iv), p. 123; (6.5), (6.13) (dual index of A_{E_δ} = norm of the conductor)"]
theorem ramifiedDualIndexConductor_proved : RamifiedDualIndexConductor F :=
  ramifiedDualIndexConductor_of_dyadic ramifiedDualIndexConductorDyadic

/-- **Gan–Hanke–Yu 2001, Proposition 7.5 (the mass formula for $\mathrm{SO}$ in even rank $n\ge4$), unconditional:** for $Q_0$
nondegenerate and totally positive definite over a totally real number field $F$, with $\mathcal O_F^n$ maximal,
$\sum_i 1/\#\Gamma_i = 2^{-(n/2)[F:\mathbb Q]}\cdot L\cdot 2\cdot\prod_v\lambda_v$ (`lMotiveEven`, `lambdaGHYEvenAt`). -/
@[kb "ganhankeyu2001" "Proposition 7.5, p. 119 (unconditional)"]
theorem ghy_prop75_proved [IsTotallyReal F] (hn : 4 ≤ n) (heven : Even n)
    (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (hmax : StdIsMaximal Q₀) :
    ∑' i : DC Q₀, ((Nat.card (unitGroup Q₀ i) : ℝ≥0∞))⁻¹ =
      ENNReal.ofReal (((2 : ℝ) ^ ((n / 2) * Module.finrank ℚ F))⁻¹ * lMotiveEven Q₀ (n / 2) * 2 *
        ∏' v : HeightOneSpectrum (𝓞 F), lambdaGHYEvenAt v Q₀) :=
  ghy_prop75_of_dyadic ramifiedDualIndexConductorDyadic hn heven Q₀ hQ hpd hmax

end QuadFormsKB.Hanke2005
