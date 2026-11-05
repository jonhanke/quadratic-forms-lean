/-
# The ramified anisotropic binary kernel at a dyadic place: the `ram` half

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005), (3.3);
G. Shimura, *An exact mass formula for orthogonal groups*, Duke Math. J. 97 (1999), §3.2, Lemma 3.7(2), Prop. 3.9;
O. T. O'Meara, *Introduction to quadratic forms*, §63A, §93.

`DyadicRamifiedBinaryDensity` has two fields: `ram` (the place ramifies in $F_\mathfrak p(\sqrt{-\det H_N/4})$) and
`density`. The field `ram` is **proved** here, purely locally: for an anisotropic maximal binary $N$ over
$\mathfrak o_\mathfrak p$ with a value of unit norm and a primitive vector $w$ with $\pi\,\|\,N(w)$, the number
$4N(x)N(w)$ has odd valuation $2e+1$ ($e = \operatorname{ord}2$), while
$$4N(x)N(w)\,c^2 = X^2 - u\,Y^2,\qquad u = 1+4y,\ X = B\,c,\ Y = 2\det[x\,w],$$
if $\mathfrak p$ were unramified, and a value $X^2-uY^2$ of the norm form of the unramified algebra $F_\mathfrak p(\sqrt u)$
has even valuation (`norm_sq_sub_even`, from the Hensel criterion `isSquare_one_sub_four_mul_iff`) when $u$ is not a
square, whereas for $u$ a square $N$ would be isotropic over $F_\mathfrak p$ (`exists_isotropic_of_sq`).

The remaining density is then the smaller named input `DyadicRamifiedBinarySelfDensity` and
`dyadicRamifiedBinaryDensity_of_selfDensity` assembles `DyadicRamifiedBinaryDensity`.
-/
import QuadFormsKB.Literature.Hanke2005.DensityDyadicKernelAniso

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR QuadFormsKB.LocalDensity.HypFrame QuadFormsKB.Tamagawa
  QuadFormsKB.Lattices QuadForm

section Alg

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **The Hensel step:** if $u = 1+4y$ is not a square in $\mathfrak o$ ($\pi\mid2$), then $\pi\nmid s^2+s-y$ for
every $s\in\mathfrak o$ (the Artin–Schreier criterion `isSquare_one_sub_four_mul_iff`). -/
theorem not_dvd_of_not_isSquare (h2 : ¬ IsUnit (2 : 𝔬)) (y : 𝔬) (hns : ¬ IsSquare (1 + 4 * y : 𝔬)) (s : 𝔬) :
    ¬ NF.π v ∣ s ^ 2 + s - y := by
  have hπ := NF.irreducible_π v
  have h2π := pi_dvd_two_of_not_isUnit v h2
  have h20 := two_ne_zero_O v
  intro hs
  apply hns
  rw [show (1 + 4 * y : 𝔬) = 1 - 4 * (-y) by ring, isSquare_one_sub_four_mul_iff hπ h2π h20]
  have hc := charP_residueField_two hπ h2π
  have h2F : (2 : IsLocalRing.ResidueField 𝔬) = 0 := CharTwo.two_eq_zero
  refine ⟨IsLocalRing.residue 𝔬 s, ?_⟩
  have h := (res_eq_zero_iff' hπ _).2 hs
  simp only [map_sub, map_add, map_pow, map_neg] at h ⊢
  linear_combination h + (IsLocalRing.residue 𝔬 y) * h2F

/-- **Values of $t^2-u$ have even $\pi$-adic order** ($u = 1+4y$ not a square, $\pi\mid 2$): for every $t\in\mathfrak o$,
$t^2-u = \pi^{2j}\cdot(\text{unit})$. *Proof:* put $z = t-1$, so $t^2-u = z^2+2z-4y$. If $\pi^e\mid z$ ($e = \operatorname{ord}2$)
then $z = 2s$ and $t^2-u = 4(s^2+s-y)$ with $\pi\nmid s^2+s-y$; otherwise $z = \pi^jz_1$ with $j<e$ and $z^2$ dominates. -/
@[kb "omeara1963" "§63A, 63:3–63:5 (quadratic defect of unit squares in characteristic 2 residue)"]
theorem sq_sub_eq_pow_mul_unit (h2 : ¬ IsUnit (2 : 𝔬)) (y : 𝔬) (hns : ¬ IsSquare (1 + 4 * y : 𝔬)) (t : 𝔬) :
    ∃ j : ℕ, ∃ w : 𝔬, IsUnit w ∧ t ^ 2 - (1 + 4 * y) = NF.π v ^ (2 * j) * w := by
  have hπ := NF.irreducible_π v
  have h2π := pi_dvd_two_of_not_isUnit v h2
  have h20 := two_ne_zero_O v
  obtain ⟨e, ⟨w₀, hw₀⟩, he'⟩ := exists_pow_dvd_not_dvd (NF.π v) hπ h20
  have hw₀u : IsUnit w₀ := dvr_isUnit_of_not_dvd hπ fun h => he' (by
    rw [hw₀, pow_succ]; exact mul_dvd_mul_left _ h)
  obtain ⟨w₁, hw₁⟩ := hw₀u.exists_right_inv
  by_cases hz : NF.π v ^ e ∣ t - 1
  · obtain ⟨z₂, hz₂⟩ := hz
    have hs : t = 1 + 2 * (w₁ * z₂) := by
      have : (2 : 𝔬) * (w₁ * z₂) = NF.π v ^ e * z₂ := by
        rw [hw₀]; linear_combination (NF.π v ^ e * z₂) * hw₁
      rw [this]; linear_combination hz₂
    refine ⟨e, w₀ ^ 2 * ((w₁ * z₂) ^ 2 + (w₁ * z₂) - y), ?_, ?_⟩
    · exact (hw₀u.pow 2).mul (dvr_isUnit_of_not_dvd hπ (not_dvd_of_not_isSquare v h2 y hns _))
    · rw [hs]
      have h4 : (4 : 𝔬) = NF.π v ^ (2 * e) * w₀ ^ 2 := by
        rw [pow_mul', show (4 : 𝔬) = 2 ^ 2 by norm_num, hw₀]; ring
      linear_combination (((w₁ * z₂) ^ 2 + (w₁ * z₂) - y)) * h4
  · have hz0 : t - 1 ≠ 0 := fun h => hz (by rw [h]; exact dvd_zero _)
    obtain ⟨j, ⟨z₁, hz₁⟩, hj'⟩ := exists_pow_dvd_not_dvd (NF.π v) hπ hz0
    have hz₁u : IsUnit z₁ := dvr_isUnit_of_not_dvd hπ fun h => hj' (by
      rw [hz₁, pow_succ]; exact mul_dvd_mul_left _ h)
    have hje : j < e := by
      by_contra hge
      exact hz ((pow_dvd_pow _ (not_lt.mp hge)).trans ⟨z₁, hz₁⟩)
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hje
    -- `e = j + d + 1`
    refine ⟨j, z₁ ^ 2 + NF.π v ^ (d + 1) * (w₀ * z₁ - NF.π v ^ (d + 1) * w₀ ^ 2 * y), ?_, ?_⟩
    · refine dvr_isUnit_of_not_dvd hπ fun h => ?_
      have h1 : NF.π v ∣ NF.π v ^ (d + 1) * (w₀ * z₁ - NF.π v ^ (d + 1) * w₀ ^ 2 * y) :=
        dvd_mul_of_dvd_left (dvd_pow_self _ (Nat.succ_ne_zero d)) _
      have := dvd_sub h h1
      rw [add_sub_cancel_right] at this
      exact hπ.not_isUnit (isUnit_of_dvd_unit (hπ.prime.dvd_of_dvd_pow this) (hz₁u))
    · have ht : t = 1 + NF.π v ^ j * z₁ := by linear_combination hz₁
      have h2e : (2 : 𝔬) = NF.π v ^ (j + d + 1) * w₀ := hw₀
      rw [ht]
      have h4 : (4 : 𝔬) = (NF.π v ^ (j + d + 1) * w₀) ^ 2 := by rw [← h2e]; norm_num
      calc (1 + NF.π v ^ j * z₁) ^ 2 - (1 + 4 * y)
          = (NF.π v ^ j * z₁) ^ 2 + 2 * (NF.π v ^ j * z₁) - 4 * y := by ring
        _ = _ := by
          rw [h4]
          rw [h2e]
          ring

/-- $\|Z\|^2 = Q^{2m}$ for $Z\ne0$, with $Q = N\mathfrak p$. -/
theorem norm_sq_eq_zpow_even {Z : Fv} (hZ : Z ≠ 0) :
    ∃ m : ℤ, ‖Z‖ ^ 2 = (Ideal.absNorm v.asIdeal : ℝ) ^ (2 * m) := by
  refine ⟨WithZero.log (Valued.v Z), ?_⟩
  rw [LocalZeta.norm_eq_absNorm_pow v hZ, ← zpow_natCast, ← _root_.zpow_mul]
  congr 1; push_cast; ring

/-- **The norm form of the unramified algebra takes values of even valuation:** if $u = 1+4y$ is not a square in
$\mathfrak o$ ($\pi\mid2$) then for $(X,Y)\ne(0,0)$ in $F_\mathfrak p^2$, $\|X^2-uY^2\| = N\mathfrak p^{\,2m}$ for an integer $m$.
*Proof:* if $\|X\|\ne\|Y\|$ the larger term wins; if $\|X\| = \|Y\|$ then $t = X/Y\in\mathfrak o$ and
`sq_sub_eq_pow_mul_unit` applies to $t^2-u$. -/
@[kb "omeara1963" "§63A, 63:3–63:5 (norm form of the unramified quadratic extension); §92"]
theorem norm_sq_sub_even (h2 : ¬ IsUnit (2 : 𝔬)) (y : 𝔬) (hns : ¬ IsSquare (1 + 4 * y : 𝔬)) {X Y : Fv}
    (hXY : X ≠ 0 ∨ Y ≠ 0) :
    ∃ m : ℤ, ‖X ^ 2 - (((1 + 4 * y : 𝔬)) : Fv) * Y ^ 2‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (2 * m) := by
  have hπ := NF.irreducible_π v
  have h2π := pi_dvd_two_of_not_isUnit v h2
  have hu : IsUnit (1 + 4 * y : 𝔬) := dvr_isUnit_of_not_dvd hπ fun h => by
    have h4 : NF.π v ∣ 4 * y := dvd_mul_of_dvd_left (h2π.trans ⟨2, by norm_num⟩) _
    have := dvd_sub h h4
    rw [add_sub_cancel_right] at this
    exact hπ.not_isUnit (isUnit_of_dvd_one this)
  have hu1 : ‖(((1 + 4 * y : 𝔬)) : Fv)‖ = 1 := by
    have := norm_pi_pow_mul_unit v 0 hu
    simpa using this
  have hQ1 : 1 < (Ideal.absNorm v.asIdeal : ℝ) := by
    rw [← NF.q_completion, DensitySD.q_eq v]; exact one_lt_normQ v
  have hQ0 : 0 < (Ideal.absNorm v.asIdeal : ℝ) := lt_trans zero_lt_one hQ1
  by_cases hX : X = 0
  · have hY : Y ≠ 0 := hXY.resolve_left (not_not.mpr hX)
    obtain ⟨m, hm⟩ := norm_sq_eq_zpow_even v hY
    refine ⟨m, ?_⟩
    rw [hX, zero_pow two_ne_zero, zero_sub, norm_neg, norm_mul, norm_pow, hu1, one_mul, hm]
  by_cases hY : Y = 0
  · obtain ⟨m, hm⟩ := norm_sq_eq_zpow_even v hX
    refine ⟨m, ?_⟩
    rw [hY, zero_pow two_ne_zero, mul_zero, sub_zero, norm_pow, hm]
  by_cases hn : ‖X‖ = ‖Y‖
  · have hnt : ‖X / Y‖ ≤ 1 := by rw [norm_div, hn, div_self (norm_ne_zero_iff.2 hY)]
    have hvt : Valued.v (X / Y) ≤ 1 := Valued.toNormedField.norm_le_one_iff.mp hnt
    set t : 𝔬 := ⟨X / Y, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hvt⟩ with ht
    obtain ⟨j, w, hw, hjw⟩ := sq_sub_eq_pow_mul_unit v h2 y hns t
    have e : X ^ 2 - (((1 + 4 * y : 𝔬)) : Fv) * Y ^ 2 = Y ^ 2 * (((t ^ 2 - (1 + 4 * y) : 𝔬)) : Fv) := by
      push_cast
      have : ((t : 𝔬) : Fv) = X / Y := rfl
      rw [this]; field_simp
    obtain ⟨m, hm⟩ := norm_sq_eq_zpow_even v hY
    refine ⟨m - j, ?_⟩
    rw [e, hjw, norm_mul, norm_pow, norm_pi_pow_mul_unit v (2 * j) hw, NF.q_completion, hm,
      show 2 * (m - j) = 2 * m - ((2 * j : ℕ) : ℤ) by push_cast; ring, zpow_sub₀ hQ0.ne', zpow_natCast,
      div_eq_mul_inv]
  · have hne : ‖X ^ 2‖ ≠ ‖-((((1 + 4 * y : 𝔬)) : Fv) * Y ^ 2)‖ := by
      rw [norm_neg, norm_mul, norm_pow, norm_pow, hu1, one_mul]
      exact fun h => hn ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h)
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_neg, norm_mul, norm_pow,
      norm_pow, hu1, one_mul]
    rcases le_total (‖X‖ ^ 2) (‖Y‖ ^ 2) with h | h
    · obtain ⟨m, hm⟩ := norm_sq_eq_zpow_even v hY
      exact ⟨m, by rw [max_eq_right h, hm]⟩
    · obtain ⟨m, hm⟩ := norm_sq_eq_zpow_even v hX
      exact ⟨m, by rw [max_eq_left h, hm]⟩

end Alg

section Binary

/-- **The discriminant identity for two vectors:** for a binary form $N$ and $x,w$,
$B(x,w)^2 - 4N(x)N(w) = -\det H_N\cdot\det[x\ w]^2$. -/
theorem polar_sq_sub_four_mul {A : Type*} [CommRing A] (N : QuadForm A 2) (x w : Fin 2 → A) :
    (x ⬝ᵥ (N.hessian *ᵥ w)) ^ 2 - 4 * N.eval x * N.eval w =
      -(N.hessian.det * (x 0 * w 1 - x 1 * w 0) ^ 2) := by
  rw [Tamagawa.bil_binary, Tamagawa.eval_binary, Tamagawa.eval_binary, Tamagawa.det_hessian_binary]
  ring

/-- **A square discriminant gives an isotropic vector:** if $N(p)\ne0$, $p,q$ are independent and
$B(p,q)^2-4N(p)N(q)$ is a square $r^2$ in a field with $2\ne0$, then $N$ has a nonzero zero
$z = \frac{r-B}{2N(p)}\,p+q$ (a root of $N(Xp+q) = N(p)X^2+BX+N(q)$). -/
@[kb "omeara1963" "§58 (isotropic binary spaces: square discriminant), §93"]
theorem exists_isotropic_of_sq {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (M : QuadForm K 2) (p q : Fin 2 → K)
    (hδ : p 0 * q 1 - p 1 * q 0 ≠ 0) (ha : M.eval p ≠ 0) (r : K)
    (hr : r ^ 2 = (p ⬝ᵥ (M.hessian *ᵥ q)) ^ 2 - 4 * M.eval p * M.eval q) :
    ∃ z : Fin 2 → K, z ≠ 0 ∧ M.eval z = 0 := by
  set a := M.eval p with ha'
  set c := M.eval q with hc'
  set B := p ⬝ᵥ (M.hessian *ᵥ q) with hB
  set X := (r - B) / (2 * a) with hXdef
  have hX : 2 * a * X = r - B := by rw [hXdef]; field_simp
  refine ⟨X • p + q, ?_, ?_⟩
  · intro h0
    apply hδ
    have h0' : X * p 0 + q 0 = 0 := by simpa using congrFun h0 0
    have h1' : X * p 1 + q 1 = 0 := by simpa using congrFun h0 1
    linear_combination p 0 * h1' - p 1 * h0'
  · have key : (4 * a) * (X ^ 2 * a + c + X * B) = 0 := by
      linear_combination (2 * a * X + (r - B) + 2 * B) * hX + hr
    have h4a : 4 * a ≠ 0 := mul_ne_zero (by
      rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2) ha
    have := (mul_eq_zero.mp key).resolve_left h4a
    rw [eval_add_hessian, eval_smul_sq, smul_dotProduct, ← hB, smul_eq_mul]
    linear_combination this

end Binary

section Main

variable {F : Type} [Field F] [NumberField F]

/-- **The ramified anisotropic binary kernel is ramified** (the `ram` field of `DyadicRamifiedBinaryDensity`, now
proved): for an anisotropic maximal binary form $N$ over $\mathfrak o_\mathfrak p$ at a dyadic place, not unimodular and
not with all values in $\mathfrak p$, the place $\mathfrak p$ is **not** unramified in $F_\mathfrak p(\sqrt{-\det H_N/4})$.
*Proof:* choose $x$ with $\pi\nmid N(x)$ and $w$ primitive with $\pi\mid N(w)$ (otherwise $N$ is unimodular); maximality
gives $\pi^2\nmid N(w)$, so $4N(x)N(w)$ has the odd valuation $2e+1$. If $-\det H_N/4\cdot c^2 = u = 1+4y$, then
$4N(x)N(w)c^2 = (Bc)^2 - u(2\det[x\,w])^2$. For $u$ a non-square this has even valuation (`norm_sq_sub_even`); for $u$ a
square the discriminant $B^2-4N(x)N(w)$ is a square and $N$ is isotropic over $F_\mathfrak p$ (`exists_isotropic_of_sq`). -/
@[kb "omeara1963" "§63A, 63:3–63:5 (quadratic defect); §93 (binary lattices)"]
theorem ramBinary_ram (v : HeightOneSpectrum (𝓞 F))
    (h2 : ¬ IsUnit (2 : v.adicCompletionIntegers F))
    (N : QuadForm (v.adicCompletionIntegers F) 2) (hN : N.Nondegenerate)
    (hmax : MaxProp v (N.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))))
    (han : ∀ y : Fin 2 → v.adicCompletion F,
        (N.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).eval y = 0 → y = 0)
    (hD : ‖((N.hessian.det : v.adicCompletionIntegers F) : v.adicCompletion F)‖⁻¹ ≠ 1)
    (hnot : ¬ ∀ y, NF.π v ∣ N.eval y) :
    ¬ IsUnramSqrt v ((-1) ^ (2 / 2) * (((N.hessian.det : v.adicCompletionIntegers F) : v.adicCompletion F) / 2 ^ 2)) := by
  rintro ⟨c₀, hc₀, y, hyu, hyeq⟩
  have hπ := NF.irreducible_π v
  have h2π := pi_dvd_two_of_not_isUnit v h2
  have h20 := two_ne_zero_O v
  have han' := aniso_integral v N han
  have hmax' := hmax_of_maxProp v h2 N hmax han'
  have hQ1 : 1 < (Ideal.absNorm v.asIdeal : ℝ) := by
    rw [← NF.q_completion, DensitySD.q_eq v]; exact one_lt_normQ v
  have hQ0 : 0 < (Ideal.absNorm v.asIdeal : ℝ) := lt_trans zero_lt_one hQ1
  have hcoe : ∀ z : v.adicCompletionIntegers F,
      ((z : v.adicCompletionIntegers F) : v.adicCompletion F) =
        algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) z := fun _ => rfl
  obtain ⟨x, hx⟩ : ∃ x, ¬ NF.π v ∣ N.eval x := by
    by_contra h; exact hnot fun y => by_contra fun hy => h ⟨y, hy⟩
  obtain ⟨w, hw, hw'⟩ : ∃ w, NF.π v ∣ N.eval w ∧ ¬ ∀ i, NF.π v ∣ w i := by
    by_contra hcon0
    have hcon : ∀ w, NF.π v ∣ N.eval w → ∀ i, NF.π v ∣ w i := fun w hw i => by
      by_contra hi; exact hcon0 ⟨w, hw, fun h => hi (h i)⟩
    apply hD
    have hu := isUnit_det_of_aniso hπ h2π N hcon
    have := norm_pi_pow_mul_unit v 0 hu
    simp only [pow_zero, one_mul, inv_one] at this
    rw [this, inv_one]
  have hc2 : ¬ NF.π v ^ 2 ∣ N.eval w := fun h => hw' (hmax' w h)
  obtain ⟨c', hc'⟩ := hw
  have hc'u : IsUnit c' := dvr_isUnit_of_not_dvd hπ fun ⟨d, hd⟩ => hc2 ⟨d, by rw [hc', hd]; ring⟩
  have hau : IsUnit (N.eval x) := dvr_isUnit_of_not_dvd hπ hx
  obtain ⟨e, ⟨w₀, hw₀⟩, he'⟩ := exists_pow_dvd_not_dvd (NF.π v) hπ h20
  have hw₀u : IsUnit w₀ := dvr_isUnit_of_not_dvd hπ fun h => he' (by
    rw [hw₀, pow_succ]; exact mul_dvd_mul_left _ h)
  have h4ac : (4 * N.eval x * N.eval w : v.adicCompletionIntegers F) =
      NF.π v ^ (2 * e + 1) * (w₀ ^ 2 * N.eval x * c') := by
    rw [hc', show (4 : v.adicCompletionIntegers F) = 2 ^ 2 by norm_num, hw₀]; ring
  have hn4 : ‖((4 * N.eval x * N.eval w : v.adicCompletionIntegers F) : v.adicCompletion F)‖ =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-((2 * e + 1 : ℕ) : ℤ)) := by
    rw [h4ac, norm_pi_pow_mul_unit v _ (((hw₀u.pow 2).mul hau).mul hc'u), NF.q_completion, _root_.zpow_neg,
      zpow_natCast]
  have hodd : Odd (-((2 * e + 1 : ℕ) : ℤ)) := ⟨-(e : ℤ) - 1, by push_cast; ring⟩
  set a := N.eval x with ha_def
  set c := N.eval w with hc_def
  set B := x ⬝ᵥ (N.hessian *ᵥ w) with hB_def
  set δ : v.adicCompletionIntegers F := x 0 * w 1 - x 1 * w 0 with hδ_def
  set D := N.hessian.det with hD_def
  have hid : B ^ 2 - 4 * a * c = -(D * δ ^ 2) := polar_sq_sub_four_mul N x w
  -- `δ ≠ 0`
  have hδ0 : δ ≠ 0 := by
    intro h0
    have hBsq : B ^ 2 = 4 * a * c := by rw [h0] at hid; linear_combination hid
    have hnB : ‖((B : v.adicCompletionIntegers F) : v.adicCompletion F)‖ ^ 2 =
        (Ideal.absNorm v.asIdeal : ℝ) ^ (-((2 * e + 1 : ℕ) : ℤ)) := by
      rw [← hn4, ← hBsq]; push_cast; rw [norm_pow]
    by_cases hB0 : ((B : v.adicCompletionIntegers F) : v.adicCompletion F) = 0
    · rw [hB0, norm_zero] at hnB
      have := zpow_pos hQ0 (-((2 * e + 1 : ℕ) : ℤ))
      rw [← hnB] at this
      norm_num at this
    · exact norm_sq_ne_odd_pow v hB0 hodd hnB
  have hδ' : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) δ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (v.adicCompletionIntegers F) (v.adicCompletion F))).mpr hδ0
  have hid' : (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) B) ^ 2 -
      4 * algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) a *
        algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) c =
      -(algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) D *
        algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) δ ^ 2) := by
    have := congrArg (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) hid
    simp only [map_sub, map_pow, map_mul, map_neg, map_ofNat] at this
    exact this
  have h22 : ((-1 : v.adicCompletion F)) ^ (2 / 2) = -1 := by norm_num
  rw [h22] at hyeq
  have hy2 : -(algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) D) * c₀ ^ 2 =
      4 * (1 + 4 * algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) y) := by
    rw [hcoe, hcoe] at hyeq
    rw [← hyeq]; ring
  by_cases hsq : IsSquare (1 + 4 * y : v.adicCompletionIntegers F)
  · obtain ⟨ρ, hρ⟩ := hsq
    have hρ' : 1 + 4 * algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) y =
        algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ρ *
          algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ρ := by
      have := congrArg (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) hρ
      simp only [map_add, map_mul, map_one, map_ofNat] at this
      exact this
    set M := N.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) with hM
    set p : Fin 2 → v.adicCompletion F := fun i => algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (x i)
      with hp
    set q : Fin 2 → v.adicCompletion F := fun i => algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (w i)
      with hq
    have hMp : M.eval p = algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) a :=
      eval_map_comp' _ N x
    have hMq : M.eval q = algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) c :=
      eval_map_comp' _ N w
    have hMB : p ⬝ᵥ (M.hessian *ᵥ q) = algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) B := by
      rw [hM, hessian_map_eq]
      simp [hp, hq, hB_def, dotProduct, Matrix.mulVec]
    have hδp : p 0 * q 1 - p 1 * q 0 =
        algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) δ := by
      simp [hp, hq, hδ_def]
    have ha' : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) a ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (v.adicCompletionIntegers F) (v.adicCompletion F))).mpr
        hau.ne_zero
    have hc₀2 : c₀ ^ 2 ≠ 0 := pow_ne_zero 2 hc₀
    obtain ⟨z, hz0, hz⟩ := exists_isotropic_of_sq two_ne_zero M p q (by rw [hδp]; exact hδ')
      (by rw [hMp]; exact ha')
      (2 * algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ρ *
        algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) δ / c₀)
      (by
        rw [hMp, hMq, hMB, hid', div_pow, div_eq_iff hc₀2]
        rw [hρ'] at hy2
        linear_combination (-(algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) δ ^ 2)) * hy2)
    exact hz0 (han z hz)
  · obtain ⟨m, hm⟩ := norm_sq_sub_even v h2 y hsq
      (X := algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) B * c₀)
      (Y := 2 * algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) δ)
      (Or.inr (mul_ne_zero two_ne_zero hδ'))
    have e1 : (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) B * c₀) ^ 2 -
        (((1 + 4 * y : v.adicCompletionIntegers F)) : v.adicCompletion F) *
          (2 * algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) δ) ^ 2 =
        (((4 * a * c : v.adicCompletionIntegers F)) : v.adicCompletion F) * c₀ ^ 2 := by
      rw [hcoe, hcoe]
      simp only [map_add, map_mul, map_one, map_ofNat]
      linear_combination c₀ ^ 2 * hid' + (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) δ) ^ 2 * hy2
    rw [e1, norm_mul, norm_pow, hn4] at hm
    apply norm_sq_ne_odd_pow v hc₀ (k := 2 * m + (2 * e + 1)) ⟨m + e, by ring⟩
    have h1 : (Ideal.absNorm v.asIdeal : ℝ) ^ (-((2 * e + 1 : ℕ) : ℤ)) *
        (Ideal.absNorm v.asIdeal : ℝ) ^ ((2 * e + 1 : ℕ) : ℤ) = 1 := by
      rw [← zpow_add₀ hQ0.ne']; simp
    have hk : (2 : ℤ) * e + 1 = ((2 * e + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [zpow_add₀ hQ0.ne', ← hm, hk]
    linear_combination (-‖c₀‖ ^ 2) * h1

end Main

section Inputs

variable (F : Type) [Field F] [NumberField F]

/-- **The self-density of the ramified anisotropic binary kernel at a dyadic place** (a **named input**; Shimura 1999,
§3.2 ($t = 2$, $\mathfrak d\ne\mathfrak r$), Lemma 3.7(2), Prop. 3.9, p. 18): for an anisotropic binary form $N$ over
$\mathfrak o_\mathfrak p$ with the extension property (`MaxProp`), not unimodular, and not all of whose values lie in
$\mathfrak p$ (equivalently its residue zero space has dimension $1$), $\beta(N,N) = 4\,|\det H_N|^{-1}$
(`localDensityForm` normalization). Field: `density`. This is the `density` field of `DyadicRamifiedBinaryDensity`; the
other field, `ram`, is proved (`ramBinary_ram`). Checked by brute force over $\mathbb Z_2$ on $\langle1,2\rangle$,
$\langle1,6\rangle$, $\langle3,2\rangle$ ($\beta = 32$) and $x^2+2xy+2y^2$, $\langle1,1\rangle$ ($\beta = 16$). -/
@[kb "shimura1999" "§3.2 (t = 2, d ≠ r), Lemma 3.7(2), Prop. 3.9, p. 18 (ramified binary kernel density)"]
structure DyadicRamifiedBinarySelfDensity : Prop where
  /-- $\beta(N,N) = 4|\det H_N|^{-1}$. -/
  density : ∀ (v : HeightOneSpectrum (𝓞 F)), ¬ IsUnit (2 : v.adicCompletionIntegers F) →
    ∀ N : QuadForm (v.adicCompletionIntegers F) 2, N.Nondegenerate →
      MaxProp v (N.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))) →
      (∀ y : Fin 2 → v.adicCompletion F,
        (N.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).eval y = 0 → y = 0) →
      ‖((N.hessian.det : v.adicCompletionIntegers F) : v.adicCompletion F)‖⁻¹ ≠ 1 →
      (¬ ∀ y, NF.π v ∣ N.eval y) →
      DVR.localDensityForm N N (NF.π v) = 4 * ‖((N.hessian.det : v.adicCompletionIntegers F) : v.adicCompletion F)‖⁻¹

/-- **`DyadicRamifiedBinaryDensity` from the smaller input `DyadicRamifiedBinarySelfDensity`:** the ramification field
`ram` is proved (`ramBinary_ram`), the density field is the input. -/
@[kb "shimura1999" "§3.2 (t = 2, d ≠ r), Lemma 3.7(2), Prop. 3.9, p. 18 (ramified binary kernel)"]
theorem dyadicRamifiedBinaryDensity_of_selfDensity (I : DyadicRamifiedBinarySelfDensity F) :
    DyadicRamifiedBinaryDensity F :=
  ⟨fun v h2 N hN hmax han hD hnot => ramBinary_ram v h2 N hN hmax han hD hnot, I.density⟩

end Inputs

end QuadFormsKB.Hanke2005
