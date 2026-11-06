/-
# The ramified binary dyadic kernel: `DyadicRamifiedBinaryDensity` is proved

W. T. Gan, J. Hanke, J.-K. Yu, *On an exact mass formula of Shimura*, Duke Math. J. 107 (2001), §6, (6.3), (6.5);
G. Shimura, *An exact mass formula for orthogonal groups*, Duke Math. J. 97 (1999), §3.2, Lemma 3.7(2), Prop. 3.9.

For $r = 2$ and $E_\delta/F$ ramified, the anisotropic kernel at a dyadic place is $\mathcal O_{E_\delta}$ with a scaled norm form
$\alpha N_{E_\delta/F}$. This file proves the named input `DyadicRamifiedBinaryDensity` of `DensityDyadicKernelAniso.lean` at
**every ramification depth** (wild ramification included), purely locally:

* **Normal form** (`exists_eisForm_normal`): an anisotropic binary $N$ over $\mathfrak o$ with the extension property, not
  unimodular, and with a unit value is $\mathrm{GL}_2(\mathfrak o)$-equivalent to $a\,(x^2 + t\,xy + n\,y^2)$ with $a$ a unit,
  $\pi\mid t$, $\pi\,\|\,n$: this is $a\,N_{E/F}$ on $\mathcal O_E = \mathfrak o[\varpi]$, $\varpi^2 - t\varpi + n = 0$ Eisenstein.
* **Density** (`DyadicR2RamLevel.lean`): $\beta(N, N) = 4q^d = 4|\det H_N|^{-1}$, $\pi^d\,\|\,\det H_N$.
* **Ramification** (`DyadicR2RamNorm.lean`): $\delta = -\det H_N/4$ is not of the form $(1 + 4y)/c^2$ with $1 + 4y$ a unit.
* **Residue zero count**: $Z(\bar N) = q$ (`resZero_eisForm`): $\bar N = \bar a\,x^2$ over the residue field.

Consequently (3.3) holds at every place and Theorem 5.1 holds with no named input left below it
(`shimuraMaximalDensityRest_proved`, `theorem51_proved`).
-/
import QuadFormsKB.Literature.Hanke2005.DyadicR2RamNorm
import QuadFormsKB.Literature.Hanke2005.Unconditional
import QuadFormsKB.Literature.Hanke2005.DyadicRamifiedBinary
import QuadFormsKB.Tamagawa.SquareClassDuality

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005.R2Ram

open QuadForm LocalDensity LocalDensity.DVR

/-! ### The normal form over a dyadic discrete valuation ring -/

section Normal

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)]
  {π : R}

theorem evalB (N : QuadForm R 2) (z : Fin 2 → R) :
    N.eval z = N.coeff 0 0 * z 0 * z 0 + N.coeff 0 1 * z 0 * z 1 + N.coeff 1 1 * z 1 * z 1 := by
  simp [QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_two]

theorem detB (N : QuadForm R 2) : N.hessian.det = 4 * N.coeff 0 0 * N.coeff 1 1 - N.coeff 0 1 ^ 2 := by
  have h10 : N.coeff 1 0 = 0 := N.upper (show (0 : Fin 2) < 1 by decide)
  simp [QuadForm.hessian, det_fin_two, h10]; ring

/-- **The normal form of the ramified binary kernel** ($\pi \mid 2$): $N(Uy) = a\,N_{t,n}(y)$ with $U\in\mathrm{GL}_2(\mathfrak o)$,
$a$ a unit, $\pi\mid t$, $n = \pi w$, $w$ a unit. Hypotheses: some value of $N$ is a unit, $\det H_N$ is not a unit, and
$\pi^2\mid N(x) \Rightarrow \pi\mid x$ (maximality). -/
theorem exists_eisForm_normal (hπ : Irreducible π) (h2π : π ∣ 2) (N : QuadForm R 2)
    (hnu : ¬ ∀ y, π ∣ N.eval y) (hdet : ¬ IsUnit N.hessian.det)
    (hmax : ∀ x : Fin 2 → R, π ^ 2 ∣ N.eval x → ∀ i, π ∣ x i) :
    ∃ (U : Matrix (Fin 2) (Fin 2) R) (a t n w : R), IsUnit U.det ∧ IsUnit a ∧ π ∣ t ∧ n = π * w ∧ IsUnit w ∧
      ∀ y, N.eval (U *ᵥ y) = a * nrm t n (y 0) (y 1) := by
  classical
  have hc := charP_residueField_two hπ h2π
  push Not at hnu
  obtain ⟨x, hx⟩ := hnu
  set c00 := N.coeff 0 0
  set c01 := N.coeff 0 1
  set c11 := N.coeff 1 1
  -- a complement `e'` of `x`
  have hxu : IsUnit (x 0) ∨ IsUnit (x 1) := by
    by_contra h
    push Not at h
    have h0 : π ∣ x 0 := by by_contra h'; exact h.1 (dvr_isUnit_of_not_dvd hπ h')
    have h1 : π ∣ x 1 := by by_contra h'; exact h.2 (dvr_isUnit_of_not_dvd hπ h')
    apply hx; rw [evalB]
    exact dvd_add (dvd_add (dvd_mul_of_dvd_right h0 _) (dvd_mul_of_dvd_right h1 _)) (dvd_mul_of_dvd_right h1 _)
  obtain ⟨e0, e1, hdet0⟩ : ∃ e0 e1 : R, IsUnit (x 0 * e1 - x 1 * e0) := by
    rcases hxu with h | h
    · exact ⟨0, 1, by simpa using h⟩
    · exact ⟨1, 0, by simpa using h.neg⟩
  set D := x 0 * e1 - x 1 * e0
  set a := N.eval x with ha
  have hau : IsUnit a := dvr_isUnit_of_not_dvd hπ hx
  set b := 2 * c00 * x 0 * e0 + c01 * (x 0 * e1 + x 1 * e0) + 2 * c11 * x 1 * e1 with hb
  set c := c00 * e0 * e0 + c01 * e0 * e1 + c11 * e1 * e1 with hcdef
  have hexp : ∀ α β : R, N.eval ![α * x 0 + β * e0, α * x 1 + β * e1] = a * α ^ 2 + b * α * β + c * β ^ 2 := by
    intro α β; rw [evalB, ha, evalB]; simp only [cons_val_zero, cons_val_one]; ring
  have hdisc : 4 * a * c - b ^ 2 = D ^ 2 * N.hessian.det := by
    rw [detB, ha, evalB]; simp only [D, b, c]; ring
  -- `π ∣ b`
  have hbπ : π ∣ b := by
    by_contra hb'
    apply hdet
    have hu : IsUnit (4 * a * c - b ^ 2) := by
      refine dvr_isUnit_of_not_dvd hπ fun h => hb' ?_
      have h4 : π ∣ 4 * a * c := by
        rw [show (4 : R) * a * c = 2 * (2 * a * c) by ring]; exact dvd_mul_of_dvd_left h2π _
      have := dvd_sub h4 h
      rw [sub_sub_cancel] at this
      exact hπ.prime.dvd_of_dvd_pow this
    rw [hdisc] at hu
    exact isUnit_of_mul_isUnit_right hu
  -- a square root of `c / a` mod `π`
  obtain ⟨z, hz⟩ := FiniteField.isSquare_of_char_two (ringChar.eq (IsLocalRing.ResidueField R) 2)
    (IsLocalRing.residue R c * (IsLocalRing.residue R a)⁻¹)
  obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective z
  have hres_a : IsLocalRing.residue R a ≠ 0 := fun h => hx ((residue_eq_zero_iff_dvd hπ _).1 h)
  have hcs : π ∣ c + a * s ^ 2 := by
    rw [← residue_eq_zero_iff_dvd hπ]
    simp only [map_add, map_mul, map_pow]
    rw [pow_two, ← hz]
    field_simp
    rw [one_add_one_eq_two, CharTwo.two_eq_zero, mul_zero]
  -- the basis `x, s x + e'`
  set b' := 2 * a * s + b
  set c' := a * s ^ 2 + b * s + c
  have hb'π : π ∣ b' := dvd_add (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h2π _) _) hbπ
  have hc'π : π ∣ c' := by
    have : c' = (c + a * s ^ 2) + b * s := by simp only [c']; ring
    rw [this]; exact dvd_add hcs (dvd_mul_of_dvd_left hbπ _)
  obtain ⟨w', hw'⟩ := hc'π
  set U : Matrix (Fin 2) (Fin 2) R := !![x 0, s * x 0 + e0; x 1, s * x 1 + e1] with hU
  have hUdet : U.det = D := by simp [U, det_fin_two, D]; ring
  have hUy : ∀ y : Fin 2 → R, N.eval (U *ᵥ y) = a * y 0 ^ 2 + b' * y 0 * y 1 + c' * y 1 ^ 2 := by
    intro y
    have e : U *ᵥ y = ![(y 0 + s * y 1) * x 0 + y 1 * e0, (y 0 + s * y 1) * x 1 + y 1 * e1] := by
      ext i; fin_cases i <;> simp [U, mulVec, dotProduct, Fin.sum_univ_two] <;> ring
    rw [e, hexp]; simp only [b', c']; ring
  -- `w'` is a unit: maximality
  have hw'u : IsUnit w' := by
    refine dvr_isUnit_of_not_dvd hπ fun hπw => ?_
    have h2 : π ^ 2 ∣ N.eval (U *ᵥ ![0, 1]) := by
      rw [hUy]; simp only [cons_val_zero, cons_val_one]
      rw [hw']; obtain ⟨w'', rfl⟩ := hπw; exact ⟨w'', by ring⟩
    have h0 := hmax _ h2 0
    have h1 := hmax _ h2 1
    simp [U, mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    have : π ∣ D := by
      have e : D = x 0 * (s * x 1 + e1) - x 1 * (s * x 0 + e0) := by simp only [D]; ring
      rw [e]; exact dvd_sub (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right h0 _)
    exact hπ.not_isUnit (isUnit_of_dvd_unit this hdet0)
  obtain ⟨ai, hai⟩ := hau.exists_right_inv
  refine ⟨U, a, b' * ai, c' * ai, w' * ai, hUdet ▸ hdet0, hau, dvd_mul_of_dvd_left hb'π _,
    by rw [hw']; ring, hw'u.mul (IsUnit.of_mul_eq_one_right a hai), fun y => ?_⟩
  rw [hUy]; unfold nrm
  linear_combination (-(b' * y 0 * y 1 + c' * y 1 ^ 2)) * hai

end Normal

/-! ### The dyadic place -/

section Place

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem indexTwo_place {t n w : 𝔬} (ht : NF.π v ∣ t) (hn : n = NF.π v * w)
    (hw : IsUnit w) : IndexTwo t n := by
  have hπ := NF.irreducible_π v
  have h2K : (2 : Fv) ≠ 0 := two_ne_zero
  refine indexTwo_of_hilbert (K := Fv) hπ ht hn hw h2K
    (fun a b ha hb => HN.hilbertSymbol_mul_left_finite_nf v a b _ ha hb (delta_ne_zero hπ ht hn hw h2K))
    (fun a c _ hc => HM3.hilbertSymbol_mul_sq_left _ a _ c hc) ?_
  set δ : Fv := delta t n
  have hδ0 : δ ≠ 0 := delta_ne_zero hπ ht hn hw h2K
  have hy : (QuotientGroup.mk (Units.mk0 δ hδ0) : SqDual.SqCl Fv) ≠ 1 := by
    rw [Ne, SqDual.mk_eq_one_iff_isSquare]
    exact not_isSquare_delta hπ ht hn hw h2K
  obtain ⟨x, hx⟩ := SqDual.hilbCl_nondeg_fin v _ hy
  induction x using QuotientGroup.induction_on with
  | H x' =>
    rw [SqDual.hilbCl_mk] at hx
    exact ⟨x', x'.ne_zero, hx⟩

/-- **The data of the ramified binary kernel at a dyadic place**: the normal form $N \simeq a\,N_{t,n}$ and the exponent
$d$ with $\pi^d\,\|\,4n - t^2$, together with $\det H_N = g^2(4n - t^2)$ for some $g \in \mathfrak o$. -/
theorem ramBinary_data (h2 : ¬ IsUnit (2 : 𝔬)) (N : QuadForm 𝔬 2) (hN : N.Nondegenerate)
    (hmax : MaxProp v (N.map (algebraMap 𝔬 Fv)))
    (han : ∀ y : Fin 2 → Fv, (N.map (algebraMap 𝔬 Fv)).eval y = 0 → y = 0)
    (hD : ‖((N.hessian.det : 𝔬) : Fv)‖⁻¹ ≠ 1) (hnot : ¬ ∀ y, NF.π v ∣ N.eval y) :
    ∃ (a t n w g : 𝔬) (d : ℕ), IsUnit a ∧ NF.π v ∣ t ∧ n = NF.π v * w ∧ IsUnit w ∧
      DVR.IsGLEquiv N (a • eisForm t n) ∧ N.hessian.det = g ^ 2 * (4 * n - t ^ 2) ∧ IsUnit g ∧
      NF.π v ^ d ∣ 4 * n - t ^ 2 ∧ ¬ NF.π v ^ (d + 1) ∣ 4 * n - t ^ 2 ∧ 1 ≤ d := by
  have hπ := NF.irreducible_π v
  have h2π := pi_dvd_two_of_not_isUnit v h2
  have han' := aniso_integral v N han
  have hmax' := hmax_of_maxProp v h2 N hmax han'
  have hdet : ¬ IsUnit N.hessian.det := by
    intro hu
    apply hD
    have := norm_pi_pow_mul_unit v 0 hu
    simp only [pow_zero, one_mul, inv_one] at this
    rw [this, inv_one]
  obtain ⟨U, a, t, n, w, hU, hau, ht, hn, hw, hUy⟩ := exists_eisForm_normal hπ h2π N hnot hdet hmax'
  have hGL : DVR.IsGLEquiv N (a • eisForm t n) := ⟨U, hU, fun y => by rw [eval_smulF, eval_eisForm, hUy]⟩
  obtain ⟨u, hu, hdetGL⟩ := hGL.det_hessian
  rw [hessian_smul_det_two, det_hessian_eisForm] at hdetGL
  obtain ⟨ui, hui⟩ := hu.exists_left_inv
  set g := ui * a
  have hdetN : N.hessian.det = g ^ 2 * (4 * n - t ^ 2) := by
    have : ui ^ 2 * (a ^ 2 * (4 * n - t ^ 2)) = ui ^ 2 * (u ^ 2 * N.hessian.det) := by rw [hdetGL]
    rw [← mul_assoc, ← mul_pow, ← mul_assoc, ← mul_pow, hui, one_pow, one_mul] at this
    rw [← this]
  have hgu : IsUnit g := (IsUnit.of_mul_eq_one u hui).mul hau
  have hD0 : 4 * n - t ^ 2 ≠ 0 := fun h => hN (by rw [hdetN, h, mul_zero])
  obtain ⟨d, hd, hd'⟩ := exists_pow_dvd_not_dvd (NF.π v) hπ hD0
  have hd1 : 1 ≤ d := by
    by_contra h0
    have h0 : d = 0 := by omega
    subst h0
    apply hd'
    rw [zero_add, pow_one, hn]
    exact dvd_sub (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) (dvd_pow ht two_ne_zero)
  exact ⟨a, t, n, w, g, d, hau, ht, hn, hw, hGL, hdetN, hgu, hd, hd', hd1⟩


/-- **The ramified binary kernel: $\beta(N, N) = 4|\det H_N|^{-1}$** at a dyadic place, every ramification depth. -/
@[kb "ganhankeyu2001" "§6, (6.3), (6.5) (r = 2, E_δ ramified: the kernel is O_E with αN_{E/F}); shimura1999 Lemma 3.7(2), Prop. 3.9, p. 18"]
theorem ramBinary_density (h2 : ¬ IsUnit (2 : 𝔬)) (N : QuadForm 𝔬 2) (hN : N.Nondegenerate)
    (hmax : MaxProp v (N.map (algebraMap 𝔬 Fv)))
    (han : ∀ y : Fin 2 → Fv, (N.map (algebraMap 𝔬 Fv)).eval y = 0 → y = 0)
    (hD : ‖((N.hessian.det : 𝔬) : Fv)‖⁻¹ ≠ 1) (hnot : ¬ ∀ y, NF.π v ∣ N.eval y) :
    DVR.localDensityForm N N (NF.π v) = 4 * ‖((N.hessian.det : 𝔬) : Fv)‖⁻¹ := by
  have hπ := NF.irreducible_π v
  have h2π := pi_dvd_two_of_not_isUnit v h2
  have h20 := two_ne_zero_O v
  obtain ⟨a, t, n, w, g, d, hau, ht, hn, hw, hGL, hdetN, hgu, hd, hd', hd1⟩ :=
    ramBinary_data v h2 N hN hmax han hD hnot
  -- the local square theorem at level `2e + 1`
  obtain ⟨e, he, he'⟩ := exists_pow_dvd_not_dvd (NF.π v) hπ h20
  obtain ⟨v2, hv2, hv2u⟩ := dvr_exact hπ he he'
  have hsq : ∀ x : 𝔬, NF.π v ^ (2 * e + 1) ∣ x - 1 → IsSquare x := fun x hx =>
    isSquare_of_pow_dvd_sub_one hπ h2π h20 hv2u hv2 hx
  have hE : (eisForm t n).Nondegenerate := by
    intro h0; apply hN; rw [hdetN]; rw [det_hessian_eisForm] at h0; rw [h0, mul_zero]
  rw [localDensityForm_of_isGLEquiv v hGL,
    Tamagawa.localDensityForm_smul (eisForm t n) hE hπ (o := 0) (by simp)
      (by simpa using dvr_not_dvd_of_isUnit hπ hau),
    localDensityForm_eisForm hπ ht hn hw hd hd' hd1 (indexTwo_place v ht hn hw) hsq]
  obtain ⟨ε, hε, hεu⟩ := dvr_exact hπ hd hd'
  have hdet' : N.hessian.det = NF.π v ^ d * (g ^ 2 * ε) := by rw [hdetN, hε]; ring
  rw [hdet', norm_pi_pow_mul_unit v d ((hgu.pow 2).mul hεu), inv_inv]
  simp

/-- **The ramified binary kernel: $\mathfrak p$ ramifies in $F_\mathfrak p(\sqrt\delta)$**, $\delta = -\det H_N/4$. -/
@[kb "ganhankeyu2001" "§6, (6.3) (r = 2: E_δ = F(√δ) ramified when the residue zero space has dimension 1); omeara1963 §63A, 63:3, 63:4, p. 161"]
theorem ramBinary_ram (h2 : ¬ IsUnit (2 : 𝔬)) (N : QuadForm 𝔬 2) (hN : N.Nondegenerate)
    (hmax : MaxProp v (N.map (algebraMap 𝔬 Fv)))
    (han : ∀ y : Fin 2 → Fv, (N.map (algebraMap 𝔬 Fv)).eval y = 0 → y = 0)
    (hD : ‖((N.hessian.det : 𝔬) : Fv)‖⁻¹ ≠ 1) (hnot : ¬ ∀ y, NF.π v ∣ N.eval y) :
    ¬ IsUnramSqrt v ((-1) ^ (2 / 2) * (((N.hessian.det : 𝔬) : Fv) / 2 ^ 2)) := by
  have hπ := NF.irreducible_π v
  have h2π := pi_dvd_two_of_not_isUnit v h2
  have h20 := two_ne_zero_O v
  obtain ⟨a, t, n, w, g, d, hau, ht, hn, hw, hGL, hdetN, hgu, hd, hd', hd1⟩ :=
    ramBinary_data v h2 N hN hmax han hD hnot
  rintro ⟨c, hc, y, hy, hcy⟩
  apply not_unram_delta (K := Fv) hπ ht hn hw h2π h20
  have hg0 : ((g : 𝔬) : Fv) ≠ 0 := by
    intro h; apply hgu.ne_zero; exact_mod_cast h
  refine ⟨(g : Fv) * c, mul_ne_zero hg0 hc, y, hy, ?_⟩
  have e : algebraMap 𝔬 Fv (1 + 4 * y) = 1 + 4 * (y : Fv) := by
    rw [map_add, map_one, map_mul, map_ofNat]; rfl
  have et : algebraMap 𝔬 Fv t = (t : Fv) := rfl
  have en : algebraMap 𝔬 Fv n = (n : Fv) := rfl
  have e4 : ((4 : 𝔬) : Fv) = 4 := map_ofNat (algebraMap 𝔬 Fv) 4
  rw [e, ← hcy, hdetN, delta, et, en]
  push_cast
  rw [e4]
  ring

/-- **`DyadicRamifiedBinaryDensity` is proved** (the last named input under (3.3) and Theorem 5.1). -/
@[kb "shimura1999" "§3.2 (t = 2, d ≠ r), Lemma 3.7(2), Prop. 3.9, p. 18 (ramified binary kernel); ganhankeyu2001 §6, (6.3), (6.5)"]
theorem dyadicRamifiedBinaryDensity : DyadicRamifiedBinaryDensity F :=
  ⟨fun v => ramBinary_ram v, fun v => ramBinary_density v⟩

/-- **`DyadicRamifiedBinarySelfDensity` is proved** (the density half; the ramification half is also proved independently
in `DyadicRamifiedBinary.lean` as `Hanke2005.ramBinary_ram`). -/
@[kb "shimura1999" "§3.2 (t = 2, d ≠ r), Lemma 3.7(2), Prop. 3.9, p. 18 (ramified binary kernel density); ganhankeyu2001 §6, (6.5)"]
theorem dyadicRamifiedBinarySelfDensity : DyadicRamifiedBinarySelfDensity F :=
  ⟨fun v => ramBinary_density v⟩


open Classical in
/-- **The residue zero count of the ramified binary kernel:** $Z(\bar N) = q$ (the residue form is $\bar a\,x^2$). -/
@[kb "shimura1999" "§3.2, (3.2.1) (Z for t = 2, K ramified: q)"]
theorem resZero_ramBinary (h2 : ¬ IsUnit (2 : 𝔬)) (N : QuadForm 𝔬 2) (hN : N.Nondegenerate)
    (hmax : MaxProp v (N.map (algebraMap 𝔬 Fv)))
    (han : ∀ y : Fin 2 → Fv, (N.map (algebraMap 𝔬 Fv)).eval y = 0 → y = 0)
    (hD : ‖((N.hessian.det : 𝔬) : Fv)‖⁻¹ ≠ 1) (hnot : ¬ ∀ y, NF.π v ∣ N.eval y) :
    (LocalDensity.HypFrame.resZero (NF.π v) N : ℝ) = normQ v := by
  obtain ⟨hZ, -⟩ := kernel_base v (dyadicQuaternaryDensity F) dyadicRamifiedBinaryDensity h2 le_rfl N hN hmax han hD
    (fun h => absurd h (by decide))
  rw [hZ, zStar, if_neg (by norm_num), if_pos ⟨rfl, ramBinary_ram v h2 N hN hmax han hD hnot⟩]

open Classical in
/-- **GHY Table 3, rows $\delta\notin F^{\times2}$, $E_\delta$ ramified ($w = \pm1$), at a dyadic place, every rank $2 + 2k$:** the
maximal lattice $\Lambda_{\delta,w} = \Delta^{k}\oplus A_{E_\delta}$ of (6.5) has
$\beta(\Lambda, \Lambda) = 2[\widetilde\Lambda:\Lambda]\,\xi = 2|\det H_N|^{-1}\cdot2\prod_{i=1}^{k}(1 - q^{-2i})$ (Shimura's (3.3) in the
repository's normalization; $|\det H_N|^{-1} = q^d$, $d$ the exponent of the different of $E_\delta/F$). -/
@[kb "ganhankeyu2001" "§6, (6.5), Table 3, p. 115 (δ ∉ F^×2, E_δ ramified, w = ±1); shimura1999 Thm 8.6(3), Prop. 3.9"]
theorem ghyTable3_ramified (h2 : ¬ IsUnit (2 : 𝔬)) (N : QuadForm 𝔬 2) (hN : N.Nondegenerate)
    (hmax : MaxProp v (N.map (algebraMap 𝔬 Fv)))
    (han : ∀ y : Fin 2 → Fv, (N.map (algebraMap 𝔬 Fv)).eval y = 0 → y = 0)
    (hD : ‖((N.hessian.det : 𝔬) : Fv)‖⁻¹ ≠ 1) (hnot : ¬ ∀ y, NF.π v ∣ N.eval y) (k : ℕ) :
    DVR.localDensityForm (hypSum N k) (hypSum N k) (NF.π v) =
      2 * ‖((N.hessian.det : 𝔬) : Fv)‖⁻¹ * xiShimura (normQ v) (2 + 2 * k) 2 True False := by
  have hZ := resZero_ramBinary v h2 N hN hmax han hD hnot
  have hq : ((DVR.q 𝔬 : ℕ) : ℝ) = normQ v := DensitySD.q_eq v
  set β : ℕ → ℝ := fun j => DVR.localDensityForm (hypSum N j) (hypSum N j) (NF.π v) with hβdef
  set S : ℕ → ℝ := fun j => 2 * ‖((N.hessian.det : 𝔬) : Fv)‖⁻¹ * xiShimura (normQ v) (2 + 2 * j) 2 True False
    with hSdef
  show β k = S k
  have hZ' : zStar (normQ v) 2 True = normQ v := by simp [zStar]
  have hrec : ∀ j, β (j + 1) = rho (normQ v) 2 (zStar (normQ v) 2 True) j * β j := by
    intro j
    simp only [hβdef]
    rw [localDensityForm_hypSum_succ (NF.irreducible_π v) N hN (aniso_integral v N han) j, hq, hZ, hZ']
  have hSrec : ∀ j, S (j + 1) = rho (normQ v) 2 (zStar (normQ v) 2 True) j * S j := by
    intro j
    simp only [hSdef]
    rw [xiShimura_succ (one_lt_normQ v) (by norm_num) (by norm_num) True j]
    ring
  have h0 : β 0 = S 0 := by
    simp only [hβdef, hSdef, hypSum]
    rw [ramBinary_density v h2 N hN hmax han hD hnot]
    simp [xiShimura, ppow]
    ring
  exact eq_of_rec 0 hrec hSrec h0 k (Nat.zero_le _)

end Place

/-! ### Consequences: no named input left under (3.3) and Theorem 5.1 -/

section Consequences

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- **`DyadicKernelDensityLow` is proved** (Shimura's density of $\mathbb H^k\perp N$ at a dyadic place, $2 \le r \le 4$). -/
@[kb "hanke2005crelle" "(3.3), p. 8 (dyadic H^k ⊥ N, r = 2, 3, 4; quoting Shimura 1999, Thm 8.6(3), Prop. 3.9)"]
theorem dyadicKernelDensityLow_proved : DyadicKernelDensityLow F :=
  dyadicKernelDensityLow_of_inputs (dyadicQuaternaryDensity F) dyadicRamifiedBinaryDensity

/-- **`ShimuraMaximalDensityRest` is proved**: (3.3) at every place. -/
@[kb "hanke2005crelle" "(3.3), p. 8 (all places)"]
theorem shimuraMaximalDensityRest_proved : ShimuraMaximalDensityRest F :=
  shimuraMaximalDensityRest_of_inputs (dyadicQuaternaryDensity F) dyadicRamifiedBinaryDensity

open Lattices Tamagawa Tamagawa.Measure Tamagawa.Measure.Weil Tamagawa.LatChange Tamagawa.Indefinite in
/-- **Theorem 5.1** (Hanke thesis, pp. 16–17, with Shimura's hypothesis), with no named input. -/
@[kb "hanke2005crelle" "Theorem 5.1, pp. 16–17"]
theorem theorem51_proved (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hmax : StdIsMaximal Q₀)
    (hdet : ShimuraDetHyp Q₀) : hankeMass Q₀ hQ = ENNReal.ofReal (theorem51RHS Q₀) :=
  theorem51_of_rest shimuraMaximalDensityRest_proved hn Q₀ hQ hmax hdet

open Lattices Tamagawa Tamagawa.Measure Tamagawa.Measure.Weil Tamagawa.LatChange Tamagawa.Indefinite in
/-- **Theorem 5.1, totally definite case** (Hanke thesis, pp. 17–18), with no named input. -/
@[kb "hanke2005crelle" "Theorem 5.1, Part 1, pp. 17–18 (totally definite)"]
theorem theorem51_definite_proved [IsTotallyReal F] (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) (hmax : StdIsMaximal Q₀) (hdet : ShimuraDetHyp Q₀) :
    ∑' i : DC Q₀, ((Nat.card (unitGroup Q₀ i) : ENNReal))⁻¹ = ENNReal.ofReal (theorem51RHS Q₀) :=
  theorem51_definite_of_rest shimuraMaximalDensityRest_proved hn Q₀ hQ hpd hmax hdet

end Consequences

end QuadFormsKB.Hanke2005.R2Ram
