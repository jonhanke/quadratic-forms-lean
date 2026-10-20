/-
# Strong approximation for vectors in an isotropic space (O'Meara 104:3, isotropic case)

**Layer:** $V = F^n$ with $Q$ = `Q : QuadForm F n` over a number field $F$, its completions, and the property
`VecApprox Q` (O'Meara 1973, 104:3; `Lattices/SARotations.lean`).

**Proves** `vecApprox_of_isotropic`: **if $Q$ is nondegenerate and isotropic over $F$ and $n \ge 4$, then `VecApprox Q`**:
vectors of a given norm $a$ can be approximated at finitely many primes by global vectors of norm $a$ that are
integral at all other primes. With `rotApprox_of_vecApprox` this gives strong approximation for rotations of
isotropic spaces (`Lattices/StrongApproximationProof.lean`).

*Proof (an arithmetic replacement for O'Meara's proof of 104:3 in the isotropic case).* Write
$V = H \perp W$ with $H = Fe + Ff$ hyperbolic ($Q(se + tf + w) = st + Q(w)$, coordinates via `orthSum hypForm R`).
For the target $a$, choose $s \in F$ close to the targets' $e$-coordinates on $T$ (after perturbing the targets on the
quadric so that these are nonzero) and integral off $T$; at the finitely many primes $\mathfrak p \notin T$ dividing $s$,
$W$ is unimodular of rank $\ge 2$ and represents $a$ by some $w_\mathfrak p$ (`exists_std_evalIn_eq_unit`); choose $w \in W$
close to the targets on $T$, congruent to $w_\mathfrak p$ modulo $s$ at those primes, and integral elsewhere; then
$t = (a - Q(w))/s$ is integral off $T$ and $z = se + tf + w$ works. No class numbers, Witt index theory or
approximation at infinite places are needed (the infinite places impose no condition: $\mathbb A_f$).
-/
import QuadFormsKB.Lattices.SARotations
import QuadFormsKB.Witt.Represents

open NumberField IsDedekindDomain Matrix WithZero Topology Filter

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {m : ℕ}

/-! ### Coordinates $V = H \perp W$ -/

/-- **The hyperbolic plane** $x_0x_1$. -/
def hypForm : QuadForm F 2 := QuadForm.ofUpper ![![0, 1], ![0, 0]]

theorem evalIn_hypForm (K : Type*) [CommRing K] [Algebra F K] (x : Fin 2 → K) :
    (hypForm : QuadForm F 2).evalIn K x = x 0 * x 1 := by
  simp [hypForm, QuadForm.evalIn, QuadForm.ofUpper, Fin.sum_univ_two]

section Coords

variable {K : Type*} [CommRing K]

/-- The vector $se + tf + w$ in coordinates $(s, t, w)$. -/
def mk3 (s t : K) (w : Fin m → K) : Fin (2 + m) → K := Fin.append ![s, t] w

/-- The $e$-coordinate. -/
def sC (y : Fin (2 + m) → K) : K := y (Fin.castAdd m 0)
/-- The $f$-coordinate. -/
def tC (y : Fin (2 + m) → K) : K := y (Fin.castAdd m 1)
/-- The $W$-coordinates. -/
def wC (y : Fin (2 + m) → K) : Fin m → K := fun b => y (Fin.natAdd 2 b)

@[simp] theorem sC_mk3 (s t : K) (w : Fin m → K) : sC (mk3 s t w) = s := by simp [sC, mk3]
@[simp] theorem tC_mk3 (s t : K) (w : Fin m → K) : tC (mk3 s t w) = t := by simp [tC, mk3]
@[simp] theorem wC_mk3 (s t : K) (w : Fin m → K) : wC (mk3 s t w) = w := by
  funext b; simp [wC, mk3]

theorem mk3_coords (y : Fin (2 + m) → K) : mk3 (sC y) (tC y) (wC y) = y := by
  funext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · fin_cases a <;> simp [mk3, sC, tC]
  · simp [mk3, wC]

end Coords

theorem evalIn_orthSum_hyp (R : QuadForm F m) (K : Type*) [CommRing K] [Algebra F K] (y : Fin (2 + m) → K) :
    (QuadForm.orthSum hypForm R).evalIn K y = sC y * tC y + R.evalIn K (wC y) := by
  rw [QuadForm.evalIn_orthSum, evalIn_hypForm]
  rfl

theorem evalIn_mk3 (R : QuadForm F m) (K : Type*) [CommRing K] [Algebra F K] (s t : K) (w : Fin m → K) :
    (QuadForm.orthSum hypForm R).evalIn K (mk3 s t w) = s * t + R.evalIn K w := by
  rw [evalIn_orthSum_hyp]; simp

/-! ### Local facts about the coordinates -/

section LocalCoords

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem locVec_mk3 (s t : F) (w : Fin m → F) :
    locVec v (mk3 s t w) = mk3 (algebraMap F Fv s) (algebraMap F Fv t) (locVec v w) := by
  funext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · fin_cases a <;> simp [mk3]
  · simp [mk3]

theorem mk3_mem_std {s t : Fv} {w : Fin m → Fv} (hs : Valued.v s ≤ 1) (ht : Valued.v t ≤ 1)
    (hw : w ∈ std v) : mk3 s t w ∈ std v := by
  intro i
  rw [neg_zero, exp_zero]
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · fin_cases a
    · simpa [mk3] using hs
    · simpa [mk3] using ht
  · have := hw b
    rw [neg_zero, exp_zero] at this
    simpa [mk3] using this

theorem wC_mem_std {y : Fin (2 + m) → Fv} (hy : y ∈ std v) : wC y ∈ std v := fun _ => hy _

theorem sC_le_one {y : Fin (2 + m) → Fv} (hy : y ∈ std v) : Valued.v (sC y) ≤ 1 := by
  have := hy (Fin.castAdd m 0); rwa [neg_zero, exp_zero] at this

theorem continuous_mk3 : Continuous fun p : Fv × Fv × (Fin m → Fv) => mk3 p.1 p.2.1 p.2.2 := by
  refine continuous_pi fun i => ?_
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · fin_cases a
    · simpa [mk3] using continuous_fst
    · simp only [mk3]
      exact continuous_snd.fst
  · simp only [mk3, Fin.append_right]
    exact (continuous_apply b).comp (continuous_snd.comp continuous_snd)

theorem continuous_sC : Continuous fun y : Fin (2 + m) → Fv => sC y := continuous_apply _
theorem continuous_tC : Continuous fun y : Fin (2 + m) → Fv => tC y := continuous_apply _
theorem continuous_wC : Continuous fun y : Fin (2 + m) → Fv => wC y :=
  continuous_pi fun _ => continuous_apply _

/-- Every neighbourhood of $0$ in $F_\mathfrak p$ contains a nonzero element. -/
theorem exists_ne_zero_mem_of_mem_nhds {N : Set Fv} (hN : N ∈ 𝓝 (0 : Fv)) : ∃ c ∈ N, c ≠ 0 := by
  obtain ⟨k, hk⟩ := exists_valued_le_of_mem_nhds v hN
  refine ⟨ϖk v k, hk _ (by rw [sub_zero, valued_ϖk]), ϖk_ne_zero v k⟩

end LocalCoords

/-! ### An integral model of $W$ -/

/-- **An integral model:** $R_0 = kR$ has coefficients in $\mathcal O_F$ for some $0 \ne k \in \mathcal O_F$. -/
theorem exists_integral_model (R : QuadForm F m) :
    ∃ (R₀ : QuadForm (𝓞 F) m) (k : 𝓞 F), k ≠ 0 ∧ R₀.map (algebraMap (𝓞 F) F) = (algebraMap (𝓞 F) F k) • R := by
  classical
  obtain ⟨k, hk, hmem⟩ := exists_int_mul_mem (Finset.univ.image fun p : Fin m × Fin m => R.coeff p.1 p.2)
  have h : ∀ i j, ∃ c : 𝓞 F, algebraMap (𝓞 F) F c = (k : F) * R.coeff i j := fun i j => by
    obtain ⟨c, hc⟩ := hmem _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)
    exact ⟨c, hc⟩
  choose c hc using h
  refine ⟨QuadForm.ofUpper c, (k : 𝓞 F), by exact_mod_cast hk, ?_⟩
  ext i j
  simp only [QuadForm.map, QuadForm.ofUpper, Matrix.map_apply, Matrix.of_apply, QuadForm.smul_coeff,
    Matrix.smul_apply, smul_eq_mul, map_intCast]
  split_ifs with hij
  · rw [hc]
  · rw [map_zero, R.upper (show id j < id i from not_le.mp hij), mul_zero]

theorem evalIn_smulForm (K : Type*) [CommRing K] [Algebra F K] (c : F) (R : QuadForm F m) (x : Fin m → K) :
    (c • R).evalIn K x = algebraMap F K c * R.evalIn K x := by
  simp only [QuadForm.evalIn, QuadForm.smul_coeff, Matrix.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

section GoodW

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

variable {R : QuadForm F m} {R₀ : QuadForm (𝓞 F) m} {k : 𝓞 F}
  (hR₀ : R₀.map (algebraMap (𝓞 F) F) = (algebraMap (𝓞 F) F k) • R)

include hR₀

theorem evalIn_model (x : Fin m → Fv) :
    (R₀.map (algebraMap (𝓞 F) F)).evalIn Fv x = algebraMap (𝓞 F) Fv k * R.evalIn Fv x := by
  rw [hR₀, evalIn_smulForm, ← IsScalarTower.algebraMap_apply]

theorem valued_k (hk : k ∉ v.asIdeal) : Valued.v (algebraMap (𝓞 F) Fv k) = 1 := by
  rw [valued_algebraMap_int, HeightOneSpectrum.intValuation_eq_one_iff]; exact hk

/-- **$W$ is integral on $\mathfrak o_\mathfrak p^m$ at a good prime.** -/
theorem valued_evalIn_le_one (hk : k ∉ v.asIdeal) {x : Fin m → Fv} (hx : x ∈ std v) :
    Valued.v (R.evalIn Fv x) ≤ 1 := by
  set y : Fin m → 𝔬 := fun i => ⟨x i, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (by
    have := hx i; rwa [neg_zero, exp_zero] at this)⟩
  have hxy : x = fun i => ((y i : 𝔬) : Fv) := rfl
  have h1 := Tamagawa.evalIn_coe_o v R₀ y
  rw [← hxy, evalIn_model v hR₀] at h1
  have h2 : Valued.v (((LocalDensity.NF.Qp v R₀).eval y : 𝔬) : Fv) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (LocalDensity.NF.Qp v R₀ |>.eval y).2
  rw [← h1, map_mul, valued_k v hR₀ hk, one_mul] at h2
  exact h2

/-- **$W$ represents every unit at a good prime** ($\mathfrak p \nmid 2k\det H(R_0)$, $m \ge 2$). -/
theorem exists_std_evalIn_eq_of_model (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (hk : k ∉ v.asIdeal)
    (hdet : R₀.hessian.det ∉ v.asIdeal) (hm : 2 ≤ m) {a : Fv} (ha : Valued.v a = 1) :
    ∃ x ∈ std v, R.evalIn Fv x = a := by
  have hu : Valued.v (algebraMap (𝓞 F) Fv k * a) = 1 := by rw [map_mul, valued_k v hR₀ hk, ha, one_mul]
  obtain ⟨x, hx, hxe⟩ := exists_std_evalIn_eq_unit v R₀ h2 hdet hm hu
  refine ⟨x, hx, ?_⟩
  rw [evalIn_model v hR₀] at hxe
  have hk0 : algebraMap (𝓞 F) Fv k ≠ 0 := by
    intro h0; have := valued_k v hR₀ hk; rw [h0, map_zero] at this; exact zero_ne_one this
  exact mul_left_cancel₀ hk0 hxe

end GoodW

/-! ### Perturbing the targets -/

/-- **Perturbing a target on the quadric** so that its $e$-coordinate is nonzero: every neighbourhood $S$ of $z$
(with $Q(z) \ne 0$) contains, in its interior, a point $z'$ with $Q(z') = Q(z)$ and $s(z') \ne 0$. -/
theorem exists_perturb (R : QuadForm F m) (v : HeightOneSpectrum (𝓞 F)) {z : Fin (2 + m) → v.adicCompletion F}
    {S : Set (Fin (2 + m) → v.adicCompletion F)} (hS : S ∈ 𝓝 z)
    (ha : (QuadForm.orthSum hypForm R).evalIn (v.adicCompletion F) z ≠ 0) :
    ∃ z' ∈ interior S, (QuadForm.orthSum hypForm R).evalIn (v.adicCompletion F) z' =
      (QuadForm.orthSum hypForm R).evalIn (v.adicCompletion F) z ∧ sC z' ≠ 0 := by
  set a := (QuadForm.orthSum hypForm R).evalIn (v.adicCompletion F) z with ha'
  have hint : interior S ∈ 𝓝 z := interior_mem_nhds.mpr hS
  by_cases hs : sC z ≠ 0
  · exact ⟨z, mem_interior_iff_mem_nhds.mpr hS, rfl, hs⟩
  rw [not_not] at hs
  have hRa : R.evalIn (v.adicCompletion F) (wC z) = a := by
    rw [ha', evalIn_orthSum_hyp, hs, zero_mul, zero_add]
  by_cases ht : tC z = 0
  · have hp : Continuous fun δ : v.adicCompletion F => mk3 δ 0 (wC z) :=
      (continuous_mk3 v).comp (continuous_id.prodMk
        (continuous_const (y := ((0 : v.adicCompletion F), wC z))))
    have hp0 : mk3 (0 : v.adicCompletion F) 0 (wC z) = z := by
      conv_rhs => rw [← mk3_coords z]
      rw [hs, ht]
    have hN : (fun δ => mk3 δ 0 (wC z)) ⁻¹' interior S ∈ 𝓝 (0 : v.adicCompletion F) :=
      hp.continuousAt.preimage_mem_nhds (by rw [hp0]; exact hint)
    obtain ⟨δ, hδ, hδ0⟩ := exists_ne_zero_mem_of_mem_nhds v hN
    refine ⟨mk3 δ 0 (wC z), hδ, ?_, by simpa using hδ0⟩
    rw [evalIn_mk3, mul_zero, zero_add, hRa]
  · set t := tC z
    set w := wC z
    let p : v.adicCompletion F → Fin (2 + m) → v.adicCompletion F :=
      fun c => mk3 (-(a * c * (2 + c)) / t) t ((1 + c) • w)
    have hp : Continuous p := by
      refine (continuous_mk3 v).comp (Continuous.prodMk ?_ (continuous_const.prodMk ?_))
      · exact ((continuous_const.mul continuous_id).mul (continuous_const.add continuous_id)).neg.div_const _
      · exact (continuous_const.add continuous_id).smul continuous_const
    have hp0 : p 0 = z := by
      simp only [p, mul_zero, zero_mul, neg_zero, zero_div, add_zero, one_smul]
      conv_rhs => rw [← mk3_coords z]
      rw [hs]
    have hN : p ⁻¹' interior S ∈ 𝓝 (0 : v.adicCompletion F) :=
      hp.continuousAt.preimage_mem_nhds (by rw [hp0]; exact hint)
    have h2 : {c : v.adicCompletion F | 2 + c ≠ 0} ∈ 𝓝 (0 : v.adicCompletion F) :=
      (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds
        (isOpen_ne.mem_nhds (by simp))
    obtain ⟨c, ⟨hc1, hc2⟩, hc0⟩ := exists_ne_zero_mem_of_mem_nhds v (inter_mem hN h2)
    refine ⟨p c, hc1, ?_, ?_⟩
    · simp only [p]
      rw [evalIn_mk3, evalIn_smul' R, hRa]
      field_simp
      ring
    · simp only [p, sC_mk3]
      exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero ha hc0) hc2)) ht


section TIntegral

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

variable {R : QuadForm F m} {R₀ : QuadForm (𝓞 F) m} {k : 𝓞 F}
  (hR₀ : R₀.map (algebraMap (𝓞 F) F) = (algebraMap (𝓞 F) F k) • R) (hk : k ∉ v.asIdeal)

include hR₀ hk

/-- **$t = (a - R(w))/s$ is integral** when $w \equiv w'$ modulo $s$ and $R(w') = a$ ($R$ integral at $\mathfrak p$). -/
theorem valued_t_le_one_of_cong {S A : Fv} (hS0 : S ≠ 0) {j : ℤ} (hj : Valued.v S = exp j) (hS : Valued.v S ≤ 1)
    {W W' : Fin m → Fv} (hW' : W' ∈ std v) (hRW' : R.evalIn Fv W' = A) (hd : W - W' ∈ ball v (-j)) :
    Valued.v ((A - R.evalIn Fv W) / S) ≤ 1 := by
  set d : Fin m → Fv := S⁻¹ • (W - W') with hd'
  have hdstd : d ∈ std v := by
    intro i
    rw [neg_zero, exp_zero, hd', Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀, hj]
    have := hd i
    rw [neg_neg] at this
    calc (exp j)⁻¹ * Valued.v ((W - W') i) ≤ (exp j)⁻¹ * exp j := by gcongr
      _ = 1 := inv_mul_cancel₀ (by simp)
  have hW : W = W' + S • d := by
    rw [hd', smul_smul, mul_inv_cancel₀ hS0, one_smul]; abel
  set H := R.hessian.map (algebraMap F Fv)
  have hpol : ∀ x y : Fin m → Fv, R.evalIn Fv (x + y) = R.evalIn Fv x + R.evalIn Fv y + x ⬝ᵥ (H *ᵥ y) :=
    fun x y => by have := QuadForm.polar_eq_hessian Fv R x y; rw [← this]; ring
  have hβ : Valued.v (W' ⬝ᵥ (H *ᵥ d)) ≤ 1 := by
    have h := hpol W' d
    have e : W' ⬝ᵥ (H *ᵥ d) = R.evalIn Fv (W' + d) - R.evalIn Fv W' - R.evalIn Fv d := by rw [h]; ring
    rw [e]
    refine (Valuation.map_sub _ _ _).trans (max_le ((Valuation.map_sub _ _ _).trans (max_le ?_ ?_)) ?_)
    · exact valued_evalIn_le_one v hR₀ hk ((std v).add_mem hW' hdstd)
    · exact valued_evalIn_le_one v hR₀ hk hW'
    · exact valued_evalIn_le_one v hR₀ hk hdstd
  have e : (A - R.evalIn Fv W) / S = -(S * R.evalIn Fv d + W' ⬝ᵥ (H *ᵥ d)) := by
    rw [hW, hpol, evalIn_smul' R, mulVec_smul, dotProduct_smul, smul_eq_mul, ← hRW']
    field_simp
    ring
  rw [e, Valuation.map_neg]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ hβ)
  rw [map_mul]
  exact mul_le_one' hS (valued_evalIn_le_one v hR₀ hk hdstd)

/-- $t = (a - R(w))/s$ is integral when $s$ is a unit. -/
theorem valued_t_le_one_of_unit {S A : Fv} (hS : Valued.v S = 1) (hA : Valued.v A ≤ 1) {W : Fin m → Fv}
    (hW : W ∈ std v) : Valued.v ((A - R.evalIn Fv W) / S) ≤ 1 := by
  rw [map_div₀, hS, div_one]
  exact (Valuation.map_sub _ _ _).trans (max_le hA (valued_evalIn_le_one v hR₀ hk hW))

end TIntegral

/-! ### Strong approximation for vectors in $H \perp W$ -/

theorem hessian_smulForm (c : F) (R : QuadForm F m) : (c • R).hessian = c • R.hessian := by
  simp only [QuadForm.hessian, QuadForm.smul_coeff, Matrix.transpose_smul, smul_add]

theorem det_model_ne_zero {R : QuadForm F m} {R₀ : QuadForm (𝓞 F) m} {k : 𝓞 F} (hk : k ≠ 0)
    (hR₀ : R₀.map (algebraMap (𝓞 F) F) = (algebraMap (𝓞 F) F k) • R) (hR : R.Nondegenerate) :
    R₀.hessian.det ≠ 0 := by
  intro h0
  have h1 : (R₀.map (algebraMap (𝓞 F) F)).hessian.det = algebraMap (𝓞 F) F R₀.hessian.det := by
    rw [QuadForm.hessian_map, RingHom.map_det]; rfl
  rw [hR₀, hessian_smulForm, Matrix.det_smul, h0, map_zero] at h1
  have hk' : algebraMap (𝓞 F) F k ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
  exact mul_ne_zero (pow_ne_zero _ hk') hR h1

/-- **Strong approximation for vectors in $H \perp W$** ($W$ nondegenerate of dimension $m \ge 2$), O'Meara 104:3 in the
isotropic case. See the module docstring for the construction $z = se + tf + w$, $t = (a - Q(w))/s$. -/
theorem vecApprox_split (R : QuadForm F m) (hm : 2 ≤ m) (hR : R.Nondegenerate) :
    VecApprox (QuadForm.orthSum (hypForm : QuadForm F 2) R) := by
  classical
  intro u hu T hT z hz Z hZ
  rcases T.eq_empty_or_nonempty with rfl | ⟨v₀, hv₀⟩
  · exact ⟨u, rfl, by simp, fun v _ => hT v (Finset.notMem_empty v)⟩
  set Q' := QuadForm.orthSum (hypForm : QuadForm F 2) R with hQ'
  set a := Q'.evalIn F u with ha
  obtain ⟨R₀, k, hk0, hR₀⟩ := exists_integral_model R
  have hdet0 := det_model_ne_zero hk0 hR₀ hR
  -- good primes
  have hgood : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      (2 : 𝓞 F) ∉ v.asIdeal ∧ k ∉ v.asIdeal ∧ R₀.hessian.det ∉ v.asIdeal ∧ v.valuation F a = 1 := by
    have h2 : (2 : 𝓞 F) ≠ 0 := two_ne_zero
    filter_upwards [eventually_not_mem h2, eventually_not_mem hk0, eventually_not_mem hdet0,
      eventually_valuation_le_one a, eventually_valuation_le_one a⁻¹] with v h1 h2 h3 h4 h5
    refine ⟨h1, h2, h3, le_antisymm h4 ?_⟩
    rw [map_inv₀] at h5
    have hne : v.valuation F a ≠ 0 := by simpa using hu
    by_contra hlt
    push Not at hlt
    exact absurd h5 (not_le.mpr (one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr hne, hlt⟩))
  set B₀ := (Filter.eventually_cofinite.mp hgood).toFinset
  have hB₀ : ∀ v, v ∉ B₀ → (2 : 𝓞 F) ∉ v.asIdeal ∧ k ∉ v.asIdeal ∧ R₀.hessian.det ∉ v.asIdeal ∧
      v.valuation F a = 1 := by
    intro v hv; by_contra hc; exact hv ((Filter.eventually_cofinite.mp hgood).mem_toFinset.mpr hc)
  set T' := T ∪ B₀ with hT'
  -- the targets on `T'`
  set z₁ : ∀ v : HeightOneSpectrum (𝓞 F), Fin (2 + m) → v.adicCompletion F :=
    fun v => if v ∈ T then z v else locVec v u with hz₁def
  set Z₁ : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin (2 + m) → v.adicCompletion F) :=
    fun v => if v ∈ T then Z v else {y | y - locVec v u ∈ ball v 0} with hZ₁def
  have hZ₁ : ∀ v ∈ T', Z₁ v ∈ 𝓝 (z₁ v) := by
    intro v hv
    simp only [hZ₁def, hz₁def]
    split_ifs with h
    · exact hZ v h
    · exact ball_add_mem_nhds v _ 0
  have hz₁ : ∀ v ∈ T', Q'.evalIn (v.adicCompletion F) (z₁ v) = algebraMap F (v.adicCompletion F) a := by
    intro v hv
    simp only [hz₁def]
    split_ifs with h
    · exact hz v h
    · rw [evalIn_locVec]
  have hz₁0 : ∀ v ∈ T', Q'.evalIn (v.adicCompletion F) (z₁ v) ≠ 0 := by
    intro v hv; rw [hz₁ v hv]; exact (map_ne_zero _).mpr hu
  choose! z₂ hz₂S hz₂Q hz₂s using fun v (hv : v ∈ T') => exists_perturb R v (hZ₁ v hv) (hz₁0 v hv)
  -- the parametrization `(σ, w) ↦ σe + ((a - R(w))/σ)f + w` near the perturbed targets
  have hΦ : ∀ v ∈ T', ∃ Sg ∈ 𝓝 (sC (z₂ v)), ∃ Om ∈ 𝓝 (wC (z₂ v)), ∀ σ ∈ Sg, ∀ w ∈ Om, σ ≠ 0 ∧
      mk3 σ ((algebraMap F (v.adicCompletion F) a - R.evalIn (v.adicCompletion F) w) / σ) w ∈ Z₁ v := by
    intro v hv
    set A := algebraMap F (v.adicCompletion F) a
    have hcont : ContinuousAt (fun p : v.adicCompletion F × (Fin m → v.adicCompletion F) =>
        mk3 p.1 ((A - R.evalIn (v.adicCompletion F) p.2) / p.1) p.2) (sC (z₂ v), wC (z₂ v)) := by
      have h1 : ContinuousAt (fun p : v.adicCompletion F × (Fin m → v.adicCompletion F) =>
          (A - R.evalIn (v.adicCompletion F) p.2) / p.1) (sC (z₂ v), wC (z₂ v)) :=
        ((continuous_const.sub ((continuous_evalIn v R).comp continuous_snd)).continuousAt).div
          continuous_fst.continuousAt (hz₂s v hv)
      exact (continuous_mk3 v).continuousAt.comp (continuous_fst.continuousAt.prodMk
        (h1.prodMk continuous_snd.continuousAt))
    have hval : mk3 (sC (z₂ v)) ((A - R.evalIn (v.adicCompletion F) (wC (z₂ v))) / sC (z₂ v)) (wC (z₂ v)) =
        z₂ v := by
      have hq := hz₂Q v hv
      rw [hz₁ v hv, evalIn_orthSum_hyp] at hq
      conv_rhs => rw [← mk3_coords (z₂ v)]
      congr 1
      rw [show A = sC (z₂ v) * tC (z₂ v) + R.evalIn (v.adicCompletion F) (wC (z₂ v)) from hq.symm]
      field_simp [hz₂s v hv]
      ring
    have hmem : interior (Z₁ v) ∈ 𝓝 (mk3 (sC (z₂ v)) ((A - R.evalIn (v.adicCompletion F) (wC (z₂ v))) /
        sC (z₂ v)) (wC (z₂ v))) := by
      rw [hval]; exact isOpen_interior.mem_nhds (hz₂S v hv)
    have hne0 : {σ : v.adicCompletion F | σ ≠ 0} ∈ 𝓝 (sC (z₂ v)) := isOpen_ne.mem_nhds (hz₂s v hv)
    have hne := continuous_fst.continuousAt.preimage_mem_nhds (x := (sC (z₂ v), wC (z₂ v))) hne0
    obtain ⟨Sg, hSg, Om, hOm, hSO⟩ := mem_nhds_prod_iff.mp (inter_mem (hcont.preimage_mem_nhds hmem) hne)
    refine ⟨Sg, hSg, Om, hOm, fun σ hσ w hw => ?_⟩
    have := hSO (Set.mk_mem_prod hσ hw)
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq] at this
    exact ⟨this.2, interior_subset this.1⟩
  choose! Sg hSg Om hOm hSO using hΦ
  -- the global `s`
  obtain ⟨s, hsT, hsint⟩ := exists_scalar_approx T' (fun v => sC (z₂ v)) Sg hSg
  have hv₀T' : v₀ ∈ T' := Finset.mem_union_left _ hv₀
  have hs0 : s ≠ 0 := by
    intro h0
    have := (hSO v₀ hv₀T' _ (hsT v₀ hv₀T') _ (mem_of_mem_nhds (hOm v₀ hv₀T'))).1
    rw [h0, map_zero] at this; exact this rfl
  -- the primes `P` dividing `s` outside `T'`
  have hsinv := eventually_valuation_le_one s⁻¹
  set P := (Filter.eventually_cofinite.mp hsinv).toFinset \ T' with hP
  have hPT' : ∀ v ∈ P, v ∉ T' := fun v hv => (Finset.mem_sdiff.mp hv).2
  have hPgood : ∀ v ∈ P, v ∉ B₀ := fun v hv hB => hPT' v hv (Finset.mem_union_right _ hB)
  have hsunit : ∀ v, v ∉ T' → v ∉ P → Valued.v (algebraMap F (v.adicCompletion F) s) = 1 := by
    intro v hv hvP
    have h1 : v.valuation F s⁻¹ ≤ 1 := by
      by_contra hc
      exact hvP (Finset.mem_sdiff.mpr ⟨(Filter.eventually_cofinite.mp hsinv).mem_toFinset.mpr hc, hv⟩)
    have h2 := hsint v hv
    rw [valued_algebraMap] at h2 ⊢
    rw [map_inv₀] at h1
    have hne : v.valuation F s ≠ 0 := by simpa using hs0
    refine le_antisymm h2 ?_
    by_contra hlt
    push Not at hlt
    exact absurd h1 (not_le.mpr (one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr hne, hlt⟩))
  -- local representations of `a` by `W` at `P`
  have hrep : ∀ v ∈ P, ∃ x ∈ std v, R.evalIn (v.adicCompletion F) x = algebraMap F (v.adicCompletion F) a := by
    intro v hv
    obtain ⟨h2, hk, hd, hav⟩ := hB₀ v (hPgood v hv)
    exact exists_std_evalIn_eq_of_model v hR₀ h2 hk hd hm (by rw [valued_algebraMap]; exact hav)
  choose! w' hw'std hw'R using hrep
  have hsne : ∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (v.adicCompletion F) s ≠ 0 :=
    fun v => (map_ne_zero _).mpr hs0
  choose j hj using fun v => exists_valued_eq_exp v (hsne v)
  -- the global `w`
  obtain ⟨w, hwU, hwint⟩ := exists_vec_approx (T' ∪ P)
    (fun v => if v ∈ T' then wC (z₂ v) else w' v)
    (fun v => if v ∈ T' then Om v else {x | x - w' v ∈ ball v (-j v)})
    (by
      intro v _
      split_ifs with h
      · exact hOm v h
      · exact ball_add_mem_nhds v _ _)
  set t : F := (a - R.evalIn F w) / s with ht
  have hloct : ∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (v.adicCompletion F) t =
      (algebraMap F (v.adicCompletion F) a - R.evalIn (v.adicCompletion F) (locVec v w)) /
        algebraMap F (v.adicCompletion F) s := by
    intro v
    rw [ht, map_div₀, map_sub, evalIn_locVec]
  have hT'cases : ∀ v ∈ T', locVec v (mk3 s t w) ∈ Z₁ v := by
    intro v hvT'
    have hw := hwU v (Finset.mem_union_left _ hvT')
    simp only [hvT', ite_true] at hw
    have h := (hSO v hvT' _ (hsT v hvT') _ hw).2
    rw [locVec_mk3, hloct]
    exact h
  refine ⟨mk3 s t w, ?_, ?_, ?_⟩
  · rw [evalIn_mk3, ht]; field_simp; ring
  · intro v hv
    have h := hT'cases v (Finset.mem_union_left _ hv)
    simp only [hZ₁def, hv, ite_true] at h
    exact h
  · intro v hv
    by_cases hvT' : v ∈ T'
    · have h := hT'cases v hvT'
      simp only [hZ₁def, hv, ite_false, Set.mem_ofPred_eq] at h
      have := (std v).add_mem h (hT v hv)
      rwa [sub_add_cancel] at this
    · obtain ⟨h2, hk, -, hav⟩ := hB₀ v (fun hB => hvT' (Finset.mem_union_right _ hB))
      have hA : Valued.v (algebraMap F (v.adicCompletion F) a) ≤ 1 := by rw [valued_algebraMap, hav]
      rw [locVec_mk3]
      by_cases hvP : v ∈ P
      · have hw := hwU v (Finset.mem_union_right _ hvP)
        simp only [hvT', ite_false] at hw
        have hj0 : j v ≤ 0 := by
          have := hsint v hvT'
          rw [hj v, ← exp_zero, exp_le_exp] at this; exact this
        have hwstd : locVec v w ∈ std v := by
          have h1 : locVec v w - w' v ∈ std v := ball_anti v (by omega) hw
          have := (std v).add_mem h1 (hw'std v hvP)
          rwa [sub_add_cancel] at this
        refine mk3_mem_std v (hsint v hvT') ?_ hwstd
        rw [hloct]
        exact valued_t_le_one_of_cong v hR₀ hk (hsne v) (hj v) (hsint v hvT') (hw'std v hvP) (hw'R v hvP) hw
      · have hwstd : locVec v w ∈ std v := hwint v (by simp [hvT', hvP])
        refine mk3_mem_std v (hsint v hvT') ?_ hwstd
        rw [hloct]
        exact valued_t_le_one_of_unit v hR₀ hk (hsunit v hvT' hvP) hA hwstd

/-! ### Changing coordinates -/

section Pullback

variable {n : ℕ}

/-- Symmetrization: the upper-triangular form with coefficients $A_{ii}$ and $A_{ij} + A_{ji}$ ($i < j$) has values
$y^{\mathsf T}Ay$. -/
theorem evalIn_ofUpper_symm {R : Type*} [CommRing R] (A : Matrix (Fin m) (Fin m) R) (K : Type*) [CommRing K]
    [Algebra R K] (y : Fin m → K) :
    (QuadForm.ofUpper fun i j => if i = j then A i i else A i j + A j i).evalIn K y =
      y ⬝ᵥ (A.map (algebraMap R K) *ᵥ y) := by
  simp only [QuadForm.evalIn, QuadForm.ofUpper, Matrix.of_apply, dotProduct, mulVec, Matrix.map_apply,
    Finset.mul_sum]
  have hsplit : ∀ i j : Fin m, y i * (algebraMap R K (A i j) * y j) =
      (if i ≤ j then algebraMap R K (A i j) * y i * y j else 0) +
        (if j < i then algebraMap R K (A i j) * y i * y j else 0) := by
    intro i j
    by_cases h : i ≤ j
    · simp [h, not_lt.mpr h]; ring
    · simp [h, lt_of_not_ge h]; ring
  simp_rw [hsplit, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => if j < i then algebraMap R K (A i j) * y i * y j else 0)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hij : i = j
  · subst hij; simp
  · by_cases h : i ≤ j
    · have hlt : i < j := lt_of_le_of_ne h hij
      simp [h, hij, hlt, map_add]; ring
    · simp [h, not_lt.mpr (le_of_lt (lt_of_not_ge h))]

/-- **The pull-back** $y \mapsto Q(My)$ of $Q$ along $M \in M_{n \times m}(F)$, as a form in $m$ variables. -/
def pullbackForm (Q : QuadForm F n) (M : Matrix (Fin n) (Fin m) F) : QuadForm F m :=
  QuadForm.ofUpper fun i j => if i = j then (Mᵀ * Q.coeff * M) i i else (Mᵀ * Q.coeff * M) i j + (Mᵀ * Q.coeff * M) j i

theorem evalIn_pullback (Q : QuadForm F n) (M : Matrix (Fin n) (Fin m) F) (K : Type*) [CommRing K] [Algebra F K]
    (y : Fin m → K) : (pullbackForm Q M).evalIn K y = Q.evalIn K (M.map (algebraMap F K) *ᵥ y) := by
  rw [pullbackForm, evalIn_ofUpper_symm, QuadForm.evalIn_eq_dotProduct, Matrix.map_mul, Matrix.map_mul,
    Matrix.transpose_map, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

end Pullback

/-! ### Transfer along a global change of coordinates -/

section Transfer

variable {n : ℕ}

/-- $P \in \mathrm{GL}_n(F)$ and $P^{-1}$ are $\mathfrak p$-integral. -/
def GLInt (P : GL (Fin n) F) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  (∀ i j, Valued.v (((P : Matrix (Fin n) (Fin n) F).map (algebraMap F (v.adicCompletion F))) i j) ≤ 1) ∧
    ∀ i j, Valued.v ((((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map
      (algebraMap F (v.adicCompletion F))) i j) ≤ 1

theorem eventually_glInt (P : GL (Fin n) F) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, GLInt P v := by
  have h : ∀ (M : Matrix (Fin n) (Fin n) F), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ i j, Valued.v ((M.map (algebraMap F (v.adicCompletion F))) i j) ≤ 1 := by
    intro M
    have : ∀ i j : Fin n, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
        Valued.v ((M.map (algebraMap F (v.adicCompletion F))) i j) ≤ 1 := fun i j => by
      filter_upwards [eventually_valuation_le_one (M i j)] with v hv
      rw [Matrix.map_apply, valued_algebraMap]; exact hv
    simpa only [Filter.eventually_all] using this
  filter_upwards [h (P : Matrix (Fin n) (Fin n) F), h ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)]
    with v h1 h2
  exact ⟨h1, h2⟩

theorem map_mul_map_inv (P : GL (Fin n) F) (K : Type*) [CommRing K] [Algebra F K] :
    (P : Matrix (Fin n) (Fin n) F).map (algebraMap F K) *
      ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map (algebraMap F K) = 1 := by
  rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem continuous_mulVec_const (v : HeightOneSpectrum (𝓞 F)) (A : Matrix (Fin n) (Fin n) (v.adicCompletion F)) :
    Continuous fun y : Fin n → v.adicCompletion F => A *ᵥ y := continuous_mulVec v A

/-- **`VecApprox` is invariant under a global change of coordinates** $y \mapsto Py$: if $Q'(y) = Q(Py)$ over $F$ and
all completions, `VecApprox Q'` gives `VecApprox Q` (at the finitely many primes where $P$ or $P^{-1}$ is not
integral, approximate the integral local solution $u$). -/
theorem vecApprox_of_coords {Q Q' : QuadForm F n} (P : GL (Fin n) F)
    (hP : ∀ (K : Type) [Field K] [Algebra F K] (y : Fin n → K),
      Q'.evalIn K y = Q.evalIn K ((P : Matrix (Fin n) (Fin n) F).map (algebraMap F K) *ᵥ y))
    (hV : VecApprox Q') : VecApprox Q := by
  classical
  intro u hu T hT z hz Z hZ
  set Pm := (P : Matrix (Fin n) (Fin n) F)
  set Pi := ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  have hPPi : ∀ (K : Type) [Field K] [Algebra F K] (x : Fin n → K),
      Pm.map (algebraMap F K) *ᵥ (Pi.map (algebraMap F K) *ᵥ x) = x := by
    intro K _ _ x
    rw [mulVec_mulVec, map_mul_map_inv, one_mulVec]
  have hQQ' : ∀ (K : Type) [Field K] [Algebra F K] (x : Fin n → K),
      Q'.evalIn K (Pi.map (algebraMap F K) *ᵥ x) = Q.evalIn K x := by
    intro K _ _ x; rw [hP, hPPi]
  have hF : ∀ M : Matrix (Fin n) (Fin n) F, M.map (algebraMap F F) = M := fun M => by
    ext i j; simp
  set u' := Pi *ᵥ u with hu'
  have hQu' : Q'.evalIn F u' = Q.evalIn F u := by
    have := hQQ' F u; rwa [hF] at this
  have hgood := eventually_glInt P
  set B := (Filter.eventually_cofinite.mp hgood).toFinset
  have hB : ∀ v, v ∉ B → GLInt P v := by
    intro v hv; by_contra hc; exact hv ((Filter.eventually_cofinite.mp hgood).mem_toFinset.mpr hc)
  have hlocP : ∀ (v : HeightOneSpectrum (𝓞 F)) (y : Fin n → F),
      locVec v (Pm *ᵥ y) = Pm.map (algebraMap F (v.adicCompletion F)) *ᵥ locVec v y :=
    fun v y => locVec_mulVec v Pm y
  obtain ⟨y', hy'Q, hy'Z, hy'std⟩ := hV u' (by rw [hQu']; exact hu) (T ∪ B)
    (fun v hv => by
      have hvB : v ∉ B := fun h => hv (Finset.mem_union_right _ h)
      have hvT : v ∉ T := fun h => hv (Finset.mem_union_left _ h)
      rw [hu', locVec_mulVec]
      exact mulVec_mem_std v (hB v hvB).2 (hT v hvT))
    (fun v => if v ∈ T then Pi.map (algebraMap F (v.adicCompletion F)) *ᵥ z v else locVec v u')
    (by
      intro v _
      split_ifs with h
      · rw [hQQ', hz v h, hQu']
      · rw [evalIn_locVec])
    (fun v => if v ∈ T then {y | Pm.map (algebraMap F (v.adicCompletion F)) *ᵥ y ∈ Z v}
      else {y | Pm.map (algebraMap F (v.adicCompletion F)) *ᵥ y - locVec v u ∈ ball v 0})
    (by
      intro v _
      split_ifs with h
      · refine (continuous_mulVec_const v _).continuousAt.preimage_mem_nhds ?_
        rw [hPPi]; exact hZ v h
      · have hc := (continuous_mulVec_const v (Pm.map (algebraMap F (v.adicCompletion F)))).continuousAt
          (x := locVec v u')
        have hb := ball_add_mem_nhds v (locVec v u) 0
        have heq : Pm.map (algebraMap F (v.adicCompletion F)) *ᵥ locVec v u' = locVec v u := by
          rw [hu', locVec_mulVec, hPPi]
        have := hc.preimage_mem_nhds (by rw [heq]; exact hb)
        exact Filter.mem_of_superset this fun y hy => hy)
  refine ⟨Pm *ᵥ y', ?_, fun v hv => ?_, fun v hv => ?_⟩
  · have := hP F y'
    rw [hF] at this
    rw [← this, hy'Q, hQu']
  · have h := hy'Z v (Finset.mem_union_left _ hv)
    simp only [hv, ite_true, Set.mem_ofPred_eq] at h
    rw [hlocP]; exact h
  · rw [hlocP]
    by_cases hvB : v ∈ B
    · have h := hy'Z v (Finset.mem_union_right _ hvB)
      simp only [hv, ite_false, Set.mem_ofPred_eq] at h
      have := (std v).add_mem h (hT v hv)
      rwa [sub_add_cancel] at this
    · exact mulVec_mem_std v (hB v hvB).1 (hy'std v (by simp [hv, hvB]))

end Transfer

/-! ### Splitting off a hyperbolic plane in coordinates -/

section Split

theorem matrix_map_algebraMap_self {a b : ℕ} (M : Matrix (Fin a) (Fin b) F) : M.map (algebraMap F F) = M := by
  ext i j; simp

/-- $Q(x + y) = Q(x) + Q(y) + B(x, y)$ over $F$. -/
theorem evalIn_add_qbil (Q : QuadForm F m) (x y : Fin m → F) :
    Q.evalIn F (x + y) = Q.evalIn F x + Q.evalIn F y + qbil Q F x y := by
  have := QuadForm.polar_eq_hessian F Q x y
  rw [qbil, ← this]; ring

/-- A nondegenerate form has no nonzero vector orthogonal to everything. -/
theorem eq_zero_of_qbil_eq_zero {Q : QuadForm F m} (hQ : Q.Nondegenerate) {x : Fin m → F}
    (hx : ∀ z, qbil Q F x z = 0) : x = 0 := by
  have hdet : (Q.hessian.map (algebraMap F F)).det ≠ 0 := by
    have : Q.hessian.map (algebraMap F F) = Q.hessian := by ext i j; simp
    rw [this]; exact hQ
  apply Matrix.eq_zero_of_mulVec_eq_zero hdet
  funext i
  have := hx (Pi.single i 1)
  rw [qbil_comm, qbil, single_dotProduct, one_mul] at this
  exact this

/-- **Splitting off a hyperbolic plane in coordinates:** a nondegenerate isotropic form $Q$ in $2 + m$ variables is
$Q(Py) = y_0y_1 + R(y_2, \dots, y_{m+1})$ for some $P \in \mathrm{GL}_{2+m}(F)$ and a nondegenerate $R$ in $m$
variables, over every field $K \supseteq F$. -/
theorem exists_split_coords (Q : QuadForm F (2 + m)) (hQ : Q.Nondegenerate) (hiso : Q.IsotropicIn F) :
    ∃ (P : GL (Fin (2 + m)) F) (R : QuadForm F m), R.Nondegenerate ∧
      ∀ (K : Type) [Field K] [Algebra F K] (y : Fin (2 + m) → K),
        (QuadForm.orthSum (hypForm : QuadForm F 2) R).evalIn K y =
          Q.evalIn K ((P : Matrix (Fin (2 + m)) (Fin (2 + m)) F).map (algebraMap F K) *ᵥ y) := by
  classical
  obtain ⟨e, f, he, hf, hef⟩ := exists_hyperbolic_pair Q F hQ hiso
  have hee := qbil_e_e he hf hef
  have hff := qbil_f_f he hf hef
  have hfe := qbil_f_e he hf hef
  set L : (Fin (2 + m) → F) →ₗ[F] (Fin 2 → F) := LinearMap.pi ![bilForm Q F e, bilForm Q F f] with hL
  have hLapp : ∀ x, L x = ![qbil Q F e x, qbil Q F f x] := by
    intro x; funext i; fin_cases i <;> simp [hL, bilForm_apply]
  have hLsurj : Function.Surjective L := by
    intro c
    refine ⟨c 1 • e + c 0 • f, ?_⟩
    rw [hLapp]
    funext i
    fin_cases i <;> simp [qbil_add_right, qbil_smul_right, hee, hff, hfe, hef]
  have hW : Module.finrank F (LinearMap.ker L) = m := by
    have h := LinearMap.finrank_range_add_finrank_ker L
    rw [LinearMap.range_eq_top.mpr hLsurj, finrank_top] at h
    simp only [Module.finrank_fin_fun] at h
    omega
  set W := LinearMap.ker L
  have hmemW : ∀ x, x ∈ W ↔ qbil Q F e x = 0 ∧ qbil Q F f x = 0 := by
    intro x
    rw [LinearMap.mem_ker, hLapp]
    constructor
    · intro h; exact ⟨congrFun h 0, congrFun h 1⟩
    · rintro ⟨h0, h1⟩; funext i; fin_cases i <;> simp [h0, h1]
  set b := Module.finBasisOfFinrankEq F W hW
  set w : Fin m → (Fin (2 + m) → F) := fun i => (b i : Fin (2 + m) → F)
  have hwW : ∀ i, w i ∈ W := fun i => (b i).2
  set Wm : Matrix (Fin (2 + m)) (Fin m) F := Matrix.of fun r i => w i r
  have hWm : ∀ y : Fin m → F, Wm *ᵥ y = ∑ i, y i • w i := by
    intro y; funext r
    simp [Wm, mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hWmW : ∀ y, Wm *ᵥ y ∈ W := fun y => by
    rw [hWm]; exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hwW i)
  set cols : Fin (2 + m) → (Fin (2 + m) → F) := Fin.append ![e, f] w
  set Pm : Matrix (Fin (2 + m)) (Fin (2 + m)) F := Matrix.of fun r c => cols c r
  have hPm : ∀ y : Fin (2 + m) → F, Pm *ᵥ y = sC y • e + tC y • f + Wm *ᵥ wC y := by
    intro y
    funext r
    simp only [Pm, Wm, cols, mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_add, Fin.append_left,
      Fin.append_right, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul, sC, tC, wC]
    try simp [mul_comm]
  set R := pullbackForm Q Wm
  have hRev : ∀ y : Fin m → F, R.evalIn F y = Q.evalIn F (Wm *ᵥ y) := by
    intro y
    rw [evalIn_pullback, matrix_map_algebraMap_self]
  -- the identity over `F` 
  have hkey : ∀ y : Fin (2 + m) → F,
      (QuadForm.orthSum (hypForm : QuadForm F 2) R).evalIn F y = Q.evalIn F (Pm *ᵥ y) := by
    intro y
    rw [evalIn_orthSum_hyp, hPm, evalIn_add_qbil, hRev]
    have hx := hmemW _ |>.mp (hWmW (wC y))
    have h1 : qbil Q F (sC y • e + tC y • f) (Wm *ᵥ wC y) = 0 := by
      rw [qbil_add_left, qbil_smul_left, qbil_smul_left, hx.1, hx.2]; ring
    have h2 : Q.evalIn F (sC y • e + tC y • f) = sC y * tC y := by
      rw [evalIn_add_qbil, evalIn_smul_sq, evalIn_smul_sq, he, hf, qbil_smul_left, qbil_smul_right, hef]
      ring
    rw [h1, h2]; ring
  -- invertibility of `Pm`
  have hdet : Pm.det ≠ 0 := by
    intro h0
    obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hy0
    rw [hPm] at hy
    have hx := hmemW _ |>.mp (hWmW (wC y))
    have hs : sC y = 0 := by
      have := congrArg (qbil Q F f) hy
      rw [qbil_add_right, qbil_add_right, qbil_smul_right, qbil_smul_right, hfe, hff, hx.2] at this
      simpa [qbil] using this
    have ht : tC y = 0 := by
      have := congrArg (qbil Q F e) hy
      rw [qbil_add_right, qbil_add_right, qbil_smul_right, qbil_smul_right, hee, hef, hx.1] at this
      simpa [qbil] using this
    rw [hs, ht, zero_smul, zero_smul, zero_add, zero_add, hWm] at hy
    have hw0 : wC y = 0 := by
      have hli := b.linearIndependent
      rw [Fintype.linearIndependent_iff] at hli
      funext i
      refine hli (wC y) ?_ i
      apply Subtype.ext
      simpa [w] using hy
    rw [← mk3_coords y, hs, ht, hw0]
    funext i
    refine Fin.addCases (fun a => ?_) (fun c => ?_) i
    · fin_cases a <;> simp [mk3]
    · simp [mk3]
  set P : GL (Fin (2 + m)) F := Matrix.nonsingInvUnit Pm (isUnit_iff_ne_zero.mpr hdet)
  have hPval : (P : Matrix (Fin (2 + m)) (Fin (2 + m)) F) = Pm := rfl
  refine ⟨P, R, ?_, ?_⟩
  · -- `R` is nondegenerate
    apply QuadForm.nondegenerate_of_polar
    intro x hx
    have hpol : ∀ y, qbil Q F (Wm *ᵥ x) (Wm *ᵥ y) = 0 := by
      intro y
      have := hx y
      rw [QuadraticMap.polar, QuadForm.toQuadraticFormIn_apply, QuadForm.toQuadraticFormIn_apply,
        QuadForm.toQuadraticFormIn_apply, hRev, hRev, hRev, mulVec_add, evalIn_add_qbil] at this
      linear_combination this
    have hxW := hmemW _ |>.mp (hWmW x)
    have hall : ∀ z, qbil Q F (Wm *ᵥ x) z = 0 := by
      intro z
      set z' := z - qbil Q F z f • e - qbil Q F z e • f
      have hz'W : z' ∈ W := by
        rw [hmemW]
        constructor
        · simp only [z', qbil_sub_right, qbil_smul_right, hee, hef, qbil_comm Q F e z]; ring
        · simp only [z', qbil_sub_right, qbil_smul_right, hfe, hff, qbil_comm Q F f z]; ring
      obtain ⟨c, hc⟩ : ∃ c : Fin m → F, Wm *ᵥ c = z' := by
        refine ⟨fun i => b.repr ⟨z', hz'W⟩ i, ?_⟩
        rw [hWm]
        have h1 := b.sum_repr ⟨z', hz'W⟩
        have h2 := congrArg Subtype.val h1
        simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
        exact h2
      have hz : z = qbil Q F z f • e + qbil Q F z e • f + Wm *ᵥ c := by rw [hc]; simp [z']
      have he' : qbil Q F (Wm *ᵥ x) e = 0 := by rw [qbil_comm]; exact hxW.1
      have hf' : qbil Q F (Wm *ᵥ x) f = 0 := by rw [qbil_comm]; exact hxW.2
      rw [hz, qbil_add_right, qbil_add_right, qbil_smul_right, qbil_smul_right, hpol c, he', hf']
      ring
    have h0 := eq_zero_of_qbil_eq_zero hQ hall
    rw [hWm] at h0
    have hli := b.linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    funext i
    refine hli x ?_ i
    apply Subtype.ext
    simpa [w] using h0
  · -- the identity over every `K`
    have hform : QuadForm.orthSum (hypForm : QuadForm F 2) R = pullbackForm Q Pm := by
      apply QuadForm.ext_eval
      intro y
      change (QuadForm.orthSum (hypForm : QuadForm F 2) R).evalIn F y = (pullbackForm Q Pm).evalIn F y
      rw [hkey, evalIn_pullback, matrix_map_algebraMap_self]
    intro K _ _ y
    rw [hform, evalIn_pullback, hPval]

end Split

/-- **Strong approximation for vectors in an isotropic space** (O'Meara 104:3, isotropic case): if $Q$ is nondegenerate
and isotropic over $F$ in $n \ge 4$ variables, then `VecApprox Q`. -/
theorem vecApprox_of_isotropic {n : ℕ} (Q : QuadForm F n) (hn : 4 ≤ n) (hQ : Q.Nondegenerate)
    (hiso : Q.IsotropicIn F) : VecApprox Q := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 + k := ⟨n - 2, by omega⟩
  obtain ⟨P, R, hR, hP⟩ := exists_split_coords Q hQ hiso
  exact vecApprox_of_coords P hP (vecApprox_split R (by omega) hR)

end QuadFormsKB.Lattices
