/-
# The dual index of the maximal lattice at an unramified place, even rank (GHY 2001, (6.5), (6.13))

W. T. Gan, J. Hanke, J.-K. Yu, *On an exact mass formula of Shimura*, Duke Math. J. 107 (2001), (6.5), (6.13);
G. Shimura, *An exact mass formula for orthogonal groups*, Duke Math. J. 97 (1999), (3.2.1).

Let $\Lambda = \mathcal O_F^n$ be the maximal lattice of a nondegenerate form $Q_0$, with $n\ge4$ **even**, and let
$\mathfrak p = v$ be a finite place which is **not ramified** in $K = F(\sqrt\delta)$ (`¬ IsRamifiedAt v Q₀`). The theorem
`dualIndexAt_even_unram` says
$$[\widetilde\Lambda_\mathfrak p:\Lambda_\mathfrak p]\in\{1,\ q^2\},\qquad
t_\mathfrak p = 0\ \Rightarrow\ [\widetilde\Lambda_\mathfrak p:\Lambda_\mathfrak p]=1,$$
where $t_\mathfrak p$ (`anisoDim`) is the dimension of the anisotropic kernel of $V_\mathfrak p$ and $q = $ `normQ v`.

*Proof.* `exists_hypSum_shape` gives $Q_\mathfrak p\simeq\mathbb H^k\perp N$ with $N$ anisotropic and maximal, of dimension
$r = t_\mathfrak p\in\{0,2,4\}$ ($r$ even, $r\le4$), and $[\widetilde\Lambda:\Lambda] = \|\det H_N\|^{-1}$. For $r = 0$ this is
$1$. For $r\in\{2,4\}$: at a non-dyadic place the Jordan shape of `oddMaximalShape_at` gives $[\widetilde\Lambda:\Lambda]=q^b$,
$b\in\{1,2\}$, and $b = 1$ forces ramification (`dualIndex_nondyadic_even`); at a dyadic place the residue zero space of $N$
has dimension $s$ with $r-2\le s\le2$: $s = 2$ gives $\|\det H_N\| = q^{-2}$, $s = 0$ is unimodular, and $s = 1$ ($r = 2$)
is the ramified case (`ramBinary_ram`), excluded by the hypothesis (`dualIndex_dyadic_aniso`).
Everything is proved; no named input is used.
-/
import QuadFormsKB.Literature.Hanke2005.GHYOddDual
import QuadFormsKB.Literature.Hanke2005.ShimuraDensityAt
import QuadFormsKB.Literature.Hanke2005.DyadicR2Ram

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR QuadFormsKB.LocalDensity.HypFrame QuadFormsKB.Tamagawa
  QuadFormsKB.Lattices QuadForm

variable {F : Type} [Field F] [NumberField F]

section Pieces

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

open DensitySD in
/-- **Non-dyadic places, even rank** (O'Meara 91:2; GHY 2001 (6.5)): if $2$ is a unit at $v$, $v$ is unramified in
$K$ and $[\widetilde\Lambda:\Lambda]\ne1$ then $[\widetilde\Lambda:\Lambda]=q^2$. -/
@[kb "ganhankeyu2001" "(6.5) (the dual index of the maximal lattice, even rank, non-dyadic place)"]
theorem dualIndex_nondyadic_even {n : ℕ} (hn : 3 ≤ n) (heven : Even n) (Q₀ : QuadForm (𝓞 F) n)
    (hQ : Q₀.Nondegenerate) (hmax : StdIsMaximal Q₀) (h2 : IsUnit (2 : 𝔬))
    (hram : ¬ IsRamifiedAt v Q₀) (h1 : dualIndexAt v Q₀ ≠ 1) :
    dualIndexAt v Q₀ = (normQ v) ^ 2 := by
  obtain ⟨a, b, h, u, W, T, hu, hW, hT, hb, hχW, hequiv, hb1, hb2⟩ := oddMaximalShape_at hn Q₀ hQ hmax v h2 h1
  subst h
  have hπ := NF.irreducible_π v
  have hq := q_eq v
  obtain ⟨U, hU, hUe⟩ := hequiv
  obtain ⟨w, hwc, hD2⟩ := det_shape v h2 u hu W T hW hT (NF.Qp v Q₀) ⟨U, hU, hUe⟩
  set D := (NF.Qp v Q₀).hessian.det with hDdef
  have hnorm : ‖((D : 𝔬) : Fv)‖ = ((DVR.q 𝔬 : ℝ) ^ b)⁻¹ :=
    norm_coe_of_pow_dvd v ⟨_, hD2⟩ (by
      rw [hD2, pow_succ]
      intro hd
      exact hπ.not_isUnit (isUnit_of_dvd_unit ((mul_dvd_mul_iff_left (pow_ne_zero _ hπ.ne_zero)).1 hd) hwc))
  have hdual : dualIndexAt v Q₀ = (normQ v) ^ b := by
    unfold dualIndexAt
    rw [← hDdef, hnorm, inv_inv, hq]
  rcases hb with rfl | rfl
  · exact absurd (hb1 rfl heven).2 hram
  · exact hdual

open Classical in
/-- **Dyadic places, anisotropic kernel of dimension $2$ or $4$:** if $N$ is an anisotropic maximal form of dimension
$r\in\{2,4\}$ at a dyadic place and $\|\det H_N\|^{-1}\ne1$, then $\|\det H_N\|^{-1}=q^2$, or $r = 2$ and $v$ is ramified in
$F_v(\sqrt{-\det H_N/4})$. (Residue zero space of dimension $s$ with $r-2\le s\le2$; cf. `kernel_base`.) -/
@[kb "ganhankeyu2001" "(6.5), (6.13) (the dual index of the maximal lattice, even rank, dyadic place)"]
theorem dualIndex_dyadic_aniso (h2 : ¬ IsUnit (2 : 𝔬)) {r : ℕ} (hr : r = 2 ∨ r = 4)
    (N : QuadForm 𝔬 r) (hN : N.Nondegenerate)
    (hmax : MaxProp v (N.map (algebraMap 𝔬 Fv)))
    (han : ∀ y : Fin r → Fv, (N.map (algebraMap 𝔬 Fv)).eval y = 0 → y = 0)
    (hD : ‖dN v N‖⁻¹ ≠ 1) :
    ‖dN v N‖⁻¹ = (normQ v) ^ 2 ∨
      (r = 2 ∧ ¬ IsUnramSqrt v ((-1) ^ (r / 2) * (dN v N / 2 ^ r))) := by
  have hπ := NF.irreducible_π v
  have h2π := pi_dvd_two_of_not_isUnit v h2
  have h20 := two_ne_zero_O v
  have han' := aniso_integral v N han
  have hmax' := hmax_of_maxProp v h2 N hmax han'
  set W := resZeroSub hπ h2π h20 N han' with hW
  set s := Module.finrank (IsLocalRing.ResidueField 𝔬) W with hs
  have hq := DensitySD.q_eq v
  have hlo := le_finrank_resZeroSub_add_two hπ h2π h20 N han'
  have hhi := finrank_resZeroSub_le_two hπ h2π h20 N han' hmax'
  rw [← hW, ← hs] at hlo hhi
  have hr2 : 2 ≤ r := by omega
  rcases hr with rfl | rfl
  · rcases (show s = 0 ∨ s = 1 ∨ s = 2 by omega) with hs0 | hs1 | hs2
    · exfalso
      apply hD
      have hNan : ∀ y : Fin 2 → 𝔬, NF.π v ∣ N.eval y → ∀ i, NF.π v ∣ y i := by
        intro y hy i
        have hW0 : W = ⊥ := Submodule.finrank_eq_zero.mp (hs.symm.trans hs0)
        have hmem : (fun j => IsLocalRing.residue 𝔬 (y j)) ∈ W := by
          rw [mem_resZeroSub, eval_map_res, res_eq_zero_iff' hπ]; exact hy
        rw [hW0, Submodule.mem_bot] at hmem
        exact (res_eq_zero_iff' hπ _).1 (congrFun hmem i)
      have hu := isUnit_det_of_aniso hπ h2π N hNan
      have := norm_pi_pow_mul_unit v 0 hu
      simp only [pow_zero, one_mul, inv_one] at this
      rw [dN, this, inv_one]
    · right
      have hnot : ¬ ∀ y, NF.π v ∣ N.eval y := by
        intro hall
        have htop : W = ⊤ := by
          rw [eq_top_iff]
          intro x _
          obtain ⟨x', rfl⟩ := res_surj_vec x
          rw [mem_resZeroSub, eval_map_res, res_eq_zero_iff' hπ]
          exact hall x'
        have : s = 2 := by rw [hs, htop, finrank_top, Module.finrank_fin_fun]
        omega
      exact ⟨rfl, ramBinary_ram v h2 N hN hmax han hD hnot⟩
    · left
      have htop : W = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [← hs, hs2, Module.finrank_fin_fun])
      have hall : ∀ y, NF.π v ∣ N.eval y := by
        intro y
        have : (fun j => IsLocalRing.residue 𝔬 (y j)) ∈ W := by rw [htop]; trivial
        rwa [mem_resZeroSub, eval_map_res, res_eq_zero_iff' hπ] at this
      obtain ⟨S, hS⟩ := exists_eq_smul_of_dvd_eval hπ.ne_zero N hall
      have hSan : ∀ y : Fin 2 → 𝔬, NF.π v ∣ S.eval y → ∀ i, NF.π v ∣ y i := fun y hy i =>
        hmax' y (by rw [hS, eval_smul_form, pow_two]; exact mul_dvd_mul_left _ hy) i
      have hSu := isUnit_det_of_aniso hπ h2π S hSan
      have hdetN : N.hessian.det = NF.π v ^ 2 * S.hessian.det := by rw [hS, hessian_smul_det_two]
      have hnD : ‖dN v N‖ = ((DVR.q 𝔬 : ℝ) ^ 2)⁻¹ := by rw [dN, hdetN, norm_pi_pow_mul_unit v 2 hSu]
      rw [hnD, inv_inv, hq]
  · left
    have hs2 : s = 2 := by omega
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
    have hT'u := isUnit_det_of_aniso hπ h2π T' hT'an
    have hnD : ‖dN v N‖ = ((DVR.q 𝔬 : ℝ) ^ 2)⁻¹ := by
      rw [dN, norm_det_of_isGLEquiv v hM, Hanke2011Structure.hessian_orthSum_det, hessian_smul_det_two,
        mul_assoc]
      exact norm_pi_pow_mul_unit v 2 (hT'u.mul hTu)
    rw [hnD, inv_inv, hq]

end Pieces

section Main

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

open Classical in
/-- **The dual index of a maximal lattice of even rank at an unramified place** (GHY 2001, (6.5), (6.13); Shimura 1999,
(3.2.1)): for even $n\ge4$ and $v$ not ramified in $K = F(\sqrt\delta)$, $[\widetilde\Lambda_v:\Lambda_v]\in\{1,q^2\}$, and
it equals $1$ when the anisotropic kernel is zero. -/
@[kb "ganhankeyu2001" "(6.5), (6.13) (the dual index of the maximal lattice, even rank)"]
theorem dualIndexAt_even_unram {n : ℕ} (hn : 4 ≤ n) (heven : Even n) (Q₀ : QuadForm (𝓞 F) n)
    (hQ : Q₀.Nondegenerate) (hmax : StdIsMaximal Q₀) (hram : ¬ IsRamifiedAt v Q₀) :
    (dualIndexAt v Q₀ = 1 ∨ dualIndexAt v Q₀ = (normQ v) ^ 2) ∧ (anisoDim v Q₀ = 0 → dualIndexAt v Q₀ = 1) := by
  have hn3 : 3 ≤ n := by omega
  obtain ⟨k, r, h, N, hN, hNM, hNa, hE⟩ :=
    exists_hypSum_shape v n (NF.Qp v Q₀) (NF.nondegenerate_Qp v hQ) (maxProp_Qp v Q₀ hQ hmax)
  subst h
  have ht := anisoDim_of_hypSum v Q₀ hQ N hNa hE
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
  -- ramification of `Q₀` is ramification of the kernel
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
  rw [hdual, ht]
  have hr024 : r = 0 ∨ r = 2 ∨ r = 4 := by
    obtain ⟨j, hj⟩ := hreven
    omega
  rcases hr024 with rfl | hr
  · have h1 : ‖dN v N‖⁻¹ = 1 := by simp [dN]
    exact ⟨Or.inl h1, fun _ => h1⟩
  · have hr' : r = 2 ∨ r = 4 := by omega
    refine ⟨?_, fun h0 => absurd h0 (by omega)⟩
    by_cases hD1 : ‖dN v N‖⁻¹ = 1
    · exact Or.inl hD1
    · right
      by_cases h2 : IsUnit (2 : 𝔬)
      · have := dualIndex_nondyadic_even v hn3 heven Q₀ hQ hmax h2 hram (by rw [hdual]; exact hD1)
        rw [← hdual]; exact this
      · rcases dualIndex_dyadic_aniso v h2 hr' N hN hNM hNa hD1 with h | ⟨_, h⟩
        · exact h
        · exact absurd (hramiff.2 h) hram

end Main

end QuadFormsKB.Hanke2005
