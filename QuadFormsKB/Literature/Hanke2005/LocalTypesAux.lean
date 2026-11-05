/-
# Hanke 2005, §3 and §6: local lemmas for the local types of maximal lattices

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

At a finite place $\mathfrak p$ of the number field $F$, with $\mathfrak o = \mathfrak o_\mathfrak p$:
* `isLocalLevel_zero_of_isUnit_det`: over a discrete valuation ring, a form whose Hessian has unit determinant has
  local level $1$ ($H^{-1}$ is integral with even diagonal; at a dyadic place $n$ is even and the diagonal minors of $H$
  have odd size);
* `isUnit_det_of_dualIndexAt_eq_one`: $[\widetilde\Lambda_\mathfrak p:\Lambda_\mathfrak p] = 1$ means $\det H$ is a unit;
* `not_isRamifiedAt_of_dualIndexAt_eq_one`: then, for $n$ even, $\mathfrak p$ is unramified in
  $K = F(\sqrt{(-1)^{n/2}\det\psi})$ (dyadic: $(-1)^{n/2}\det H = B^2(1-4T)$, `DVR.exists_disc_eq_sq_mul_one_sub_four_of_level_zero`);
* `exists_val_one_hilbert_of_not_isUnramSqrt`: if $F_\mathfrak p(\sqrt x)/F_\mathfrak p$ is ramified, some $\xi$ of valuation
  $1$ has $(\xi, x)_\mathfrak p = 1$, i.e. is a norm from $F_\mathfrak p(\sqrt x)$ (O'Meara 63:11a with a unit $\Delta$ of
  quadratic defect $4\mathfrak o$, and the nondegeneracy of the Hilbert symbol).
-/
import QuadFormsKB.Literature.Hanke2005.MaximalSimilitude
import QuadFormsKB.LocalDensity.DVRLevel
import QuadFormsKB.LocalDensity.DyadicArf
import QuadFormsKB.Literature.OMeara.Sec63B
import QuadFormsKB.Tamagawa.LocalRankFive
import QuadFormsKB.Literature.Hanke2011Structure.HessianParity

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.LocalDensity

/-- **Unit determinant gives local level $1$** (any discrete valuation ring): if $\det H$ is a unit, then
$W = H^{-1}$ is symmetric with even diagonal and $HW = 1$. -/
theorem isLocalLevel_zero_of_isUnit_det {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}
    (Q : QuadForm R n) (π : R) (hdet : IsUnit Q.hessian.det) : DVR.IsLocalLevel Q π 0 := by
  classical
  have hu : IsUnit Q.hessian := (Matrix.isUnit_iff_isUnit_det _).2 hdet
  refine ⟨Q.hessian⁻¹, ?_, ?_, fun i => ?_⟩
  · rw [pow_zero, one_smul]; exact Matrix.mul_nonsing_inv _ hdet
  · rw [Matrix.transpose_nonsing_inv, DVR.hessian_transpose]
  · by_cases h2 : IsUnit (2 : R)
    · exact h2.dvd
    · have hev : ¬ Odd n := fun hodd => by
        have hm := Hanke2011Structure.hessian_det_mem_span_two_of_odd hodd Q
        rw [Ideal.mem_span_singleton] at hm
        exact h2 (isUnit_of_dvd_unit hm hdet)
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.pos; omega⟩
      have hodd : Odd m := by
        rcases Nat.even_or_odd m with h | h
        · exact absurd (by simpa [Nat.odd_add_one] using h) hev
        · exact h
      let Q' : QuadForm R m := ⟨Q.coeff.submatrix i.succAbove i.succAbove, fun a b hab => by
        have : i.succAbove b < i.succAbove a := Fin.strictMono_succAbove i hab
        exact Q.upper this⟩
      have hm := Hanke2011Structure.hessian_det_mem_span_two_of_odd hodd Q'
      rw [Ideal.mem_span_singleton] at hm
      have hsub : Q'.hessian = Q.hessian.submatrix i.succAbove i.succAbove := by
        ext a b; simp [Q', QuadForm.hessian]
      rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_fin_succ_eq_det_submatrix, ← hsub]
      simp only [smul_eq_mul]
      refine Dvd.dvd.mul_left ?_ _
      simp only [← two_mul]
      rw [Even.neg_one_pow (even_two_mul _), one_mul]
      exact hm

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **$[\widetilde\Lambda_\mathfrak p:\Lambda_\mathfrak p] = 1$ iff $\det H$ is a unit of $\mathfrak o_\mathfrak p$** (the direction
used). -/
theorem isUnit_det_of_dualIndexAt_eq_one (Q₀ : QuadForm (𝓞 F) n) (h : dualIndexAt v Q₀ = 1) :
    IsUnit (NF.Qp v Q₀).hessian.det := by
  have h1 : ‖(((NF.Qp v Q₀).hessian.det : 𝔬) : Fv)‖ = 1 := by
    unfold dualIndexAt at h
    exact inv_eq_one.1 h
  set d : 𝔬 := (NF.Qp v Q₀).hessian.det
  have hd0 : (d : Fv) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at h1; exact zero_ne_one h1
  rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  rw [QuadFormsKB.LocalZeta.norm_eq_absNorm_pow v hd0] at h1
  have hq : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hlog : WithZero.log (Valued.v (d : Fv)) = 0 :=
    (zpow_eq_one_iff_right₀ (by positivity) hq.ne').1 h1
  rw [← WithZero.exp_log ((Valued.v).ne_zero_iff.mpr hd0), hlog, WithZero.exp_zero]

/-- **Self-dual places are unramified in $K$** ($n$ even): if $[\widetilde\Lambda_\mathfrak p:\Lambda_\mathfrak p] = 1$ then
$\mathfrak p$ is not ramified in $K = F(\sqrt\delta)$. -/
theorem not_isRamifiedAt_of_dualIndexAt_eq_one (Q₀ : QuadForm (𝓞 F) n) (hn : Even n)
    (h : dualIndexAt v Q₀ = 1) : ¬ IsRamifiedAt v Q₀ := by
  unfold IsRamifiedAt
  rw [not_not]
  have hu := isUnit_det_of_dualIndexAt_eq_one v Q₀ h
  set d : 𝔬 := (NF.Qp v Q₀).hessian.det with hd
  obtain ⟨m, hm⟩ := hn
  have hn2 : n / 2 = m := by omega
  have key : algebraMap F Fv ((Q₀.map (algebraMap (𝓞 F) F)).hessian.det) = (d : Fv) := by
    rw [hd, hessian_det_cast v Q₀]
    have : (Q₀.map (algebraMap (𝓞 F) F)).hessian = Q₀.hessian.map (algebraMap (𝓞 F) F) := by
      ext i j; simp [QuadForm.hessian, QuadForm.map]
    rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rfl
  have hδ : algebraMap F Fv (discK Q₀) = (-1) ^ m * (d : Fv) / 2 ^ n := by
    simp only [discK, map_mul, map_div₀, map_pow, map_neg, map_one, map_ofNat, key, hn2]
    ring
  have hd0 : (d : Fv) ≠ 0 := by
    have := hu.ne_zero
    exact fun h0 => this (Subtype.ext h0)
  have h2F : (2 : Fv) ≠ 0 := two_ne_zero
  rw [hδ]
  unfold IsUnramSqrt
  by_cases h2 : IsUnit (2 : 𝔬)
  · obtain ⟨w, hw⟩ : ∃ w : 𝔬, 2 * w = 1 := ⟨((h2.unit⁻¹ : 𝔬ˣ) : 𝔬), by simp⟩
    have hu' : IsUnit ((-1 : 𝔬) ^ m * d * 2 ^ n) :=
      ((isUnit_one.neg.pow m).mul hu).mul (h2.pow n)
    refine ⟨2 ^ n, pow_ne_zero _ h2F, ((-1 : 𝔬) ^ m * d * 2 ^ n - 1) * w ^ 2, ?_, ?_⟩
    · have : 1 + 4 * (((-1 : 𝔬) ^ m * d * 2 ^ n - 1) * w ^ 2) = (-1 : 𝔬) ^ m * d * 2 ^ n := by
        linear_combination (((-1 : 𝔬) ^ m * d * 2 ^ n - 1) * (2 * w + 1)) * hw
      rw [this]; exact hu'
    · have hw' : (2 : Fv) * (w : Fv) = 1 := by
        have := congrArg (fun z : 𝔬 => (z : Fv)) hw
        push_cast at this
        exact this
      have h2c : ((2 : 𝔬) : Fv) = 2 := map_ofNat (algebraMap 𝔬 Fv) 2
      push_cast
      rw [h2c]
      rw [div_mul_eq_mul_div, div_eq_iff (pow_ne_zero _ h2F)]
      linear_combination (-(2 : Fv) ^ n * ((-1 : Fv) ^ m * d * 2 ^ n - 1) * (2 * w + 1)) * hw'
  · have hπ := NF.irreducible_π v
    have hπ2 : NF.π v ∣ 2 := by
      have := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hπ
      have hm2 : (2 : 𝔬) ∈ IsLocalRing.maximalIdeal 𝔬 := h2
      rw [this, Ideal.mem_span_singleton] at hm2
      exact hm2
    have hL := isLocalLevel_zero_of_isUnit_det (NF.Qp v Q₀) (NF.π v) hu
    obtain ⟨B, T, hB, heq⟩ :=
      DVR.exists_disc_eq_sq_mul_one_sub_four_of_level_zero (NF.Qp v Q₀) hπ hπ2 (NF.two_ne_zero' v) hL
    rw [hn2] at heq
    have hunit : IsUnit (1 - 4 * T) := by
      have : IsUnit (B ^ 2 * (1 - 4 * T)) := by
        rw [← heq]; exact (isUnit_one.neg.pow m).mul hu
      exact isUnit_of_mul_isUnit_right this
    have hB0 : (B : Fv) ≠ 0 := fun h0 => hB.ne_zero (Subtype.ext h0)
    have heqF : (-1 : Fv) ^ m * (d : Fv) = (B : Fv) ^ 2 * (1 - 4 * (T : Fv)) := by
      rw [← hd] at heq
      have := congrArg (fun z : 𝔬 => (z : Fv)) heq
      push_cast at this
      exact this
    refine ⟨2 ^ m / B, div_ne_zero (pow_ne_zero _ h2F) hB0, -T, ?_, ?_⟩
    · rw [show 1 + 4 * -T = 1 - 4 * T by ring]; exact hunit
    · have h2n : (2 : Fv) ^ n = 2 ^ m * 2 ^ m := by rw [hm, pow_add]
      push_cast
      rw [h2n, div_pow, mul_div_assoc', heqF]
      field_simp
      ring

/-- **A unit of quadratic defect $4\mathfrak o$ exists** at every finite place (O'Meara 63:6; for non-dyadic places
$4\mathfrak o = \mathfrak o$ is the defect of a nonsquare unit). -/
theorem exists_unit_quadDefect_four : ∃ Δ : 𝔬, IsUnit Δ ∧
    OMeara.quadDefect 𝔬 (algebraMap 𝔬 Fv Δ) = Submodule.span 𝔬 {(4 : Fv)} := by
  have h2ne : (2 : 𝔬) ≠ 0 := NF.two_ne_zero' v
  by_cases h2 : IsUnit (2 : 𝔬)
  · obtain ⟨u, hu, hud⟩ := (OMeara.exists_quadDefect_nondyadic (R := 𝔬) (F := Fv) h2).2
    refine ⟨u, hu, hud.trans ?_⟩
    obtain ⟨w, hw⟩ : ∃ w : 𝔬, 2 * w = 1 := ⟨((h2.unit⁻¹ : 𝔬ˣ) : 𝔬), by simp⟩
    apply le_antisymm
    · intro z hz
      obtain ⟨y, rfl⟩ := Submodule.mem_one.1 hz
      refine Submodule.mem_span_singleton.2 ⟨y * w ^ 2, ?_⟩
      rw [Algebra.smul_def, map_mul, mul_assoc]
      have : (algebraMap 𝔬 Fv) (w ^ 2) * 4 = 1 := by
        rw [← map_ofNat (algebraMap 𝔬 Fv) 4, ← map_mul]
        rw [show (w ^ 2 * 4 : 𝔬) = (2 * w) ^ 2 by ring, hw]; simp
      rw [this, mul_one]
    · rw [Submodule.span_le]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      exact Submodule.mem_one.2 ⟨4, by rw [hz]; exact map_ofNat (algebraMap 𝔬 Fv) 4⟩
  · obtain ⟨-, ⟨u, hu, hud⟩, -⟩ := OMeara.exists_quadDefect_dyadic (R := 𝔬) (F := Fv) h2ne h2
      (NF.irreducible_π v)
    exact ⟨u, hu, hud⟩

/-- **Hilbert-symbol step:** if every $\xi$ of valuation $1$ has $(\xi, x) = -1$, then $x\Delta$ is a square, for $\Delta$
a unit of quadratic defect $4\mathfrak o$ (O'Meara 63:11a and nondegeneracy of the Hilbert symbol). -/
theorem isSquare_mul_of_hneg {x : Fv} (hx : x ≠ 0)
    (hneg : ∀ ξ : Fv, Valued.v ξ = WithZero.exp (-1 : ℤ) → hilbertSymbol Fv ξ x = -1)
    {Δ : 𝔬} (hΔu : IsUnit Δ)
    (hΔd : OMeara.quadDefect 𝔬 (algebraMap 𝔬 Fv Δ) = Submodule.span 𝔬 {(4 : Fv)}) :
    IsSquare (x * (Δ : Fv)) := by
  classical
  have h2ne : (2 : 𝔬) ≠ 0 := NF.two_ne_zero' v
  have hvΔ : Valued.v ((Δ : 𝔬) : Fv) = 1 :=
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.1 hΔu
  have hΔ0 : ((Δ : 𝔬) : Fv) ≠ 0 := fun h0 => by rw [h0, map_zero] at hvΔ; exact zero_ne_one hvΔ
  have hπv : Valued.v ((NF.π v : 𝔬) : Fv) = WithZero.exp (-1 : ℤ) := NF.valued_π v
  have hπ0 : ((NF.π v : 𝔬) : Fv) ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hπv; exact WithZero.exp_ne_zero hπv.symm
  have hunitΔ : ∀ ε : 𝔬, IsUnit ε →
      hilbertSymbol Fv (algebraMap 𝔬 Fv ε) (algebraMap 𝔬 Fv Δ) = 1 := fun ε hε =>
    OMeara.hilbertSymbol_unit_delta (R := 𝔬) (F := Fv) h2ne hΔu hΔd hε
  have hprimeΔ : hilbertSymbol Fv (algebraMap 𝔬 Fv (NF.π v)) (algebraMap 𝔬 Fv Δ) = -1 :=
    OMeara.hilbertSymbol_prime_delta (R := 𝔬) (F := Fv) h2ne hΔu hΔd (NF.irreducible_π v)
  replace hunitΔ : ∀ ε : 𝔬, IsUnit ε → hilbertSymbol Fv (ε : Fv) (Δ : Fv) = 1 := hunitΔ
  replace hprimeΔ : hilbertSymbol Fv ((NF.π v : 𝔬) : Fv) (Δ : Fv) = -1 := hprimeΔ
  -- the character `ψ z = (z, x)(z, Δ)` is trivial
  have hψmul : ∀ a b : Fv, a ≠ 0 → b ≠ 0 →
      hilbertSymbol Fv (a * b) x * hilbertSymbol Fv (a * b) (Δ : Fv) =
        (hilbertSymbol Fv a x * hilbertSymbol Fv a (Δ : Fv)) *
          (hilbertSymbol Fv b x * hilbertSymbol Fv b (Δ : Fv)) := fun a b ha hb => by
    rw [LocalRankFive.hs_mul_left v ha hb hx, LocalRankFive.hs_mul_left v ha hb hΔ0]; ring
  have hψπ : hilbertSymbol Fv ((NF.π v : 𝔬) : Fv) x * hilbertSymbol Fv ((NF.π v : 𝔬) : Fv) (Δ : Fv) = 1 := by
    rw [hneg _ hπv, hprimeΔ]; norm_num
  have hψunit : ∀ ε : 𝔬, IsUnit ε →
      hilbertSymbol Fv (ε : Fv) x * hilbertSymbol Fv (ε : Fv) (Δ : Fv) = 1 := fun ε hε => by
    have hε0 : (ε : Fv) ≠ 0 := fun h0 => hε.ne_zero (Subtype.ext h0)
    have hve : Valued.v (ε : Fv) = 1 :=
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.1 hε
    have h1 := hneg (((NF.π v : 𝔬) : Fv) * (ε : Fv))
      (by rw [map_mul, hπv, hve, mul_one])
    rw [LocalRankFive.hs_mul_left v hπ0 hε0 hx, hneg _ hπv] at h1
    rw [hunitΔ ε hε]
    linarith
  have hψzpow : ∀ k : ℤ, hilbertSymbol Fv (((NF.π v : 𝔬) : Fv) ^ k) x *
      hilbertSymbol Fv (((NF.π v : 𝔬) : Fv) ^ k) (Δ : Fv) = 1 := by
    intro k
    induction k using Int.induction_on with
    | zero => rw [zpow_zero, LocalRankFive.hs_one_left, LocalRankFive.hs_one_left]; norm_num
    | succ k ih =>
      rw [zpow_add_one₀ hπ0, hψmul _ _ (zpow_ne_zero _ hπ0) hπ0, ih, hψπ]; norm_num
    | pred k ih =>
      have := hψmul (((NF.π v : 𝔬) : Fv) ^ (-(k : ℤ) - 1)) ((NF.π v : 𝔬) : Fv)
        (zpow_ne_zero _ hπ0) hπ0
      rw [← zpow_add_one₀ hπ0, show -(k : ℤ) - 1 + 1 = -(k : ℤ) by ring, ih, hψπ] at this
      linarith
  have hψall : ∀ z : Fv, z ≠ 0 →
      hilbertSymbol Fv z x * hilbertSymbol Fv z (Δ : Fv) = 1 := by
    intro z hz
    set k : ℤ := WithZero.log (Valued.v z) with hk
    have hvz : Valued.v z = WithZero.exp k := by
      rw [hk, WithZero.exp_log ((Valued.v).ne_zero_iff.mpr hz)]
    have hvπk : Valued.v (((NF.π v : 𝔬) : Fv) ^ k) = WithZero.exp (-k) := by
      rw [map_zpow₀, hπv, ← WithZero.exp_zsmul]; simp
    have hle : Valued.v (z * ((NF.π v : 𝔬) : Fv) ^ k) = 1 := by
      rw [map_mul, hvz, hvπk, ← WithZero.exp_add]; simp
    let ε : 𝔬 := ⟨z * ((NF.π v : 𝔬) : Fv) ^ k, by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, hle]⟩
    have hεu : IsUnit ε :=
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 hle
    have hε0 : (ε : Fv) ≠ 0 := fun h0 => hεu.ne_zero (Subtype.ext h0)
    have hz' : z = (ε : Fv) * ((NF.π v : 𝔬) : Fv) ^ (-k) := by
      show z = z * ((NF.π v : 𝔬) : Fv) ^ k * ((NF.π v : 𝔬) : Fv) ^ (-k)
      rw [mul_assoc, ← zpow_add₀ hπ0]; simp
    rw [hz', hψmul _ _ hε0 (zpow_ne_zero _ hπ0), hψunit ε hεu, hψzpow, one_mul]
  by_contra hns
  obtain ⟨y, hy0, hy⟩ := LocalRankFive.exists_hs_neg_one v (mul_ne_zero hx hΔ0) hns
  have h1 := hψall y hy0
  rw [LocalRankFive.hs_mul_right v hy0 hx hΔ0] at hy
  linarith

/-- **Square-class step:** if $x\Delta = s^2$ for a unit $\Delta$ of quadratic defect $4\mathfrak o$, then
$F_\mathfrak p(\sqrt x)/F_\mathfrak p$ is unramified. -/
theorem isUnramSqrt_of_mul_eq_sq {x : Fv} {Δ : 𝔬} (hΔu : IsUnit Δ)
    (hΔd : OMeara.quadDefect 𝔬 (algebraMap 𝔬 Fv Δ) = Submodule.span 𝔬 {(4 : Fv)}) {s : Fv}
    (hs : x * (Δ : Fv) = s * s) (hx : x ≠ 0) : IsUnramSqrt v x := by
  classical
  have h2ne : (2 : 𝔬) ≠ 0 := NF.two_ne_zero' v
  have hvΔ : Valued.v ((Δ : 𝔬) : Fv) = 1 :=
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.1 hΔu
  have hΔ0 : ((Δ : 𝔬) : Fv) ≠ 0 := fun h0 => by rw [h0, map_zero] at hvΔ; exact zero_ne_one hvΔ
  have hs0 : s ≠ 0 := fun h0 => mul_ne_zero hx hΔ0 (by rw [hs, h0, mul_zero])
  by_cases h2 : IsUnit (2 : 𝔬)
  · obtain ⟨w, hw⟩ : ∃ w : 𝔬, 2 * w = 1 := ⟨((h2.unit⁻¹ : 𝔬ˣ) : 𝔬), by simp⟩
    refine ⟨(Δ : Fv) / s, div_ne_zero hΔ0 hs0, (Δ - 1) * w ^ 2, ?_, ?_⟩
    · have : 1 + 4 * ((Δ - 1) * w ^ 2) = Δ := by
        linear_combination ((Δ - 1) * (2 * w + 1)) * hw
      rw [this]; exact hΔu
    · have hw' : (2 : Fv) * (w : Fv) = 1 := by
        have := congrArg (fun z : 𝔬 => (z : Fv)) hw
        push_cast at this
        exact this
      have h4w : (4 : Fv) * (w : Fv) ^ 2 = 1 := by linear_combination (2 * (w : Fv) + 1) * hw'
      push_cast
      rw [div_pow, ← mul_div_assoc, div_eq_iff (pow_ne_zero _ hs0)]
      have : x * (Δ : Fv) ^ 2 = s * s * Δ := by rw [← hs]; ring
      linear_combination this - (s ^ 2 * ((Δ : Fv) - 1)) * h4w
  · obtain ⟨η, hη⟩ := OMeara.exists_quadDefect_eq (R := 𝔬) (F := Fv) h2ne ((Δ : 𝔬) : Fv)
    have hη' : Submodule.span 𝔬 {((Δ : 𝔬) : Fv) - η ^ 2} = Submodule.span 𝔬 {(4 : Fv)} :=
      hη.trans hΔd
    have hmem : ((Δ : 𝔬) : Fv) - η ^ 2 ∈ Submodule.span 𝔬 {(4 : Fv)} := by
      rw [← hη']; exact Submodule.mem_span_singleton_self _
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hmem
    have hr' : (Δ : Fv) = η ^ 2 + (r : Fv) * 4 := by
      rw [Algebra.smul_def] at hr
      have : algebraMap 𝔬 Fv r * 4 = (r : Fv) * 4 := rfl
      linear_combination -hr + this
    have hle1 : ∀ z : 𝔬, Valued.v (z : Fv) ≤ 1 := fun z => z.2
    have h4 : Valued.v ((4 : 𝔬) : Fv) < 1 := by
      refine lt_of_le_of_ne (hle1 4) fun h1 => ?_
      have hu4 : IsUnit (4 : 𝔬) :=
        HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 h1
      exact h2 (isUnit_of_mul_isUnit_left (x := (2 : 𝔬)) (y := 2) (by norm_num; exact hu4))
    have h4c : ((4 : 𝔬) : Fv) = (4 : Fv) := map_ofNat (algebraMap 𝔬 Fv) 4
    have h4' : Valued.v (4 : Fv) < 1 := by rw [← h4c]; exact h4
    have hr4 : Valued.v ((r : Fv) * 4) < 1 := by
      calc Valued.v ((r : Fv) * 4) = Valued.v (r : Fv) * Valued.v (4 : Fv) := map_mul _ _ _
        _ ≤ 1 * Valued.v (4 : Fv) := mul_le_mul_left (hle1 r) _
        _ < 1 := by rw [one_mul]; exact h4'
    have hηsq : Valued.v (η ^ 2) = 1 := by
      rw [show η ^ 2 = (Δ : Fv) - (r : Fv) * 4 by linear_combination -hr',
        Valuation.map_sub_eq_of_lt_left _ (by rw [hvΔ]; exact hr4), hvΔ]
    have hη0 : η ≠ 0 := fun h0 => by rw [h0] at hηsq; simp at hηsq
    have hη1 : Valued.v η = 1 := by
      have hl : Valued.v η = WithZero.exp (WithZero.log (Valued.v η)) :=
        (WithZero.exp_log ((Valued.v).ne_zero_iff.mpr hη0)).symm
      have h2l : WithZero.exp ((2 : ℤ) • WithZero.log (Valued.v η)) = WithZero.exp 0 := by
        rw [WithZero.exp_zsmul, zpow_ofNat, ← hl, ← map_pow, hηsq, WithZero.exp_zero]
      have := WithZero.exp_injective h2l
      rw [hl, show WithZero.log (Valued.v η) = 0 by simpa using this, WithZero.exp_zero]
    have e2 : 1 + 4 * ((r : Fv) / η ^ 2) = (Δ : Fv) / η ^ 2 := by
      rw [eq_div_iff (pow_ne_zero 2 hη0), hr']
      field_simp
    obtain ⟨y, hy⟩ : ∃ y : 𝔬, (y : Fv) = (r : Fv) / η ^ 2 :=
      ⟨⟨(r : Fv) / η ^ 2, by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, hηsq, div_one]; exact hle1 r⟩, rfl⟩
    have e : ((1 + 4 * y : 𝔬) : Fv) = (Δ : Fv) / η ^ 2 := by
      push_cast
      rw [h4c, hy]
      exact e2
    refine ⟨(Δ : Fv) / (s * η), div_ne_zero hΔ0 (mul_ne_zero hs0 hη0), y, ?_, ?_⟩
    · rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one, e, map_div₀, hvΔ, hηsq,
        div_one]
    · rw [hy, e2]
      rw [div_pow, ← mul_div_assoc, div_eq_div_iff (pow_ne_zero 2 (mul_ne_zero hs0 hη0))
        (pow_ne_zero 2 hη0)]
      linear_combination ((Δ : Fv) * η ^ 2) * hs

/-- **Ramified quadratic extensions have norms of valuation $1$:** if $F_\mathfrak p(\sqrt x)/F_\mathfrak p$ is ramified
(`¬ IsUnramSqrt v x`), some $\xi$ with $v(\xi) = 1$ has $(\xi, x)_\mathfrak p = 1$. -/
theorem exists_val_one_hilbert_of_not_isUnramSqrt {x : Fv} (hx : x ≠ 0) (hr : ¬ IsUnramSqrt v x) :
    ∃ ξ : Fv, Valued.v ξ = WithZero.exp (-1 : ℤ) ∧ hilbertSymbol Fv ξ x = 1 := by
  by_contra hcon
  push Not at hcon
  have hneg : ∀ ξ : Fv, Valued.v ξ = WithZero.exp (-1 : ℤ) → hilbertSymbol Fv ξ x = -1 :=
    fun ξ hξ => (LocalRankFive.hs_pm v ξ x).resolve_left (hcon ξ hξ)
  obtain ⟨Δ, hΔu, hΔd⟩ := exists_unit_quadDefect_four v
  obtain ⟨s, hs⟩ := isSquare_mul_of_hneg v hx hneg hΔu hΔd
  exact hr (isUnramSqrt_of_mul_eq_sq v hΔu hΔd hs hx)

end QuadFormsKB.Hanke2005
