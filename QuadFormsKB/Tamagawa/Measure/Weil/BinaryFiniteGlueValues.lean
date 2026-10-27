import QuadFormsKB.Tamagawa.Measure.Weil.BinaryFiniteGlue

/-!
# The finite factor of the measure comparison for the binary torus: the values and the finite ratio

**Layer:** as in `BinaryFiniteGlue.lean`: $F$ a number field, $D\in\mathcal O_F\setminus\{0\}$, $E=F(\theta)$, $\theta^2=-D$ (`SqrtData`),
$S$ a finite set of finite places containing every $v$ with $2D\in\mathfrak p_v$, levels $k_v\ge\max(1,c_v,3s_v+2\delta_v+1)$
($c_v$ = `cv`, $|2|_v=q^{-s_v}$, $|D|_v=q^{-\delta_v}$, $q=N\mathfrak p_v$), $\lambda_v=1-\chi_E(v)/q$ (`lamL (chiE F E)`),
$\mu^\lambda_f$ = `muFin (diagForm1 D) (lamL (chiE F E))`.

**Proves**
* `muLocSO_Uloc`: $\mu^{SO}_v(U_v)=q^{c_v}\cdot q^{3s+\delta}q^{-(k+s)}$ for $U_v=\mathrm{tor}(1+\varpi^k\mathcal O_{E,v})$. *Proof:* $U_v$ contains
  the principal congruence subgroup $K_{k+s}=\mathrm{tor}(1+\varpi^kR_v)$ (`torSOK_image_window`, `coe_HR`) with index
  $[1+\varpi^k\mathcal O:1+\varpi^kR]=q^{c_v}$ (`relIndex_HR_HO`: the kernel of the torus map, the scalars, lies in the smaller window,
  `mem_winR_of_im_zero`; then `relIndex_unitWindow_cv`) and $\mu^{SO}_v(K_{k+s})=q^{3s+\delta}q^{-(k+s)}$ (`muLocSO_congSubSOBin`);
* `siegelDensity_mul_lamL`: $\alpha_v=\lambda_v$ at every $v$ with $2D\notin\mathfrak p_v$ (`chiP_eq_chiE_of_not_mem`: both characters are
  the residue symbol of $-4D$, with $\theta'=2\theta$);
* **`muFin_Kp`**: $\mu^\lambda_f(K')=\prod_{v\in S}q^{c_v}q^{3s+\delta}q^{-(k+s)}(1-\chi_E(v)/q)^{-1}$ (`muFin_boxSO_haar_of_ne_top`);
* **`muFinUnits_boxF`**: $\mu_{f,F}(N_F)=|d_F|^{-1/2}\prod_{v\in S}q^{-k}(1-q^{-1})^{-1}$ and **`muFinUnits_boxE`**:
  $\mu_{f,E}(A_f)=|d_E|^{-1/2}\prod_{v\in S}q^{-2k}(1-q^{-1})^{-1}(1-\chi_E(v)q^{-1})^{-1}$ (`muFinUnits_ideleBox_ofReal`, `omegaV_window_ratio`,
  `prod_omegaV_window_ratio`);
* **`finite_ratio`**: $\mu_{f,E}(A_f)=\text{finRatio}(D)\cdot\mu_{f,F}(N_F)\cdot\mu^\lambda_f(K')$ with
  $\text{finRatio}(D)=|N_{F/\mathbb Q}(4d)|^{-3/2}|d_F|^{-1/2}$ (the inverse of `shellRatio`), from the local identity
  $F_vK_v=E_v\,q^{c_v+2s_v+\delta_v}$, the product formula for $2$ and $D$ (`prod_qn_pow_eq`: $\prod_vq^{s_v}=2^{[F:\mathbb Q]}$,
  $\prod_vq^{\delta_v}=|N_{F/\mathbb Q}D|$) and the discriminant relation `discr_mul_prod_localIndex_sq`
  $|d_E|\bigl(\prod_vq^{c_v}\bigr)^2=4^{[F:\mathbb Q]}|d_F|^2|N_{F/\mathbb Q}D|$ (`finite_ratio_real`);
* **`exists_finiteFactor`** (all of the above together, for an arbitrary basis $(1,\delta)$ with $\delta^2=-D$):
  measurable $A_f$ and $K'$ with $K_f=N\mathbf 1_{K'}$, $\mu_{f,E}(A_f)=\text{finRatio}\cdot N\mu^\lambda_f(K')$
  and $0<N\mu^\lambda_f(K')<\infty$, at the places $2D\in\mathfrak p_v$ with the levels
  `levels`. This is the hypothesis of `torComparison_of_finiteFactor` (with `finRatio D` $=($`shellRatio D`$)^{-1}$ by definition).

Source: Weil, *Adeles and Algebraic Groups*, §2.3 and Thm 2.3.1
[unverified locators]; Neukirch, *Algebraic Number Theory*, Ch. III §2 (discriminants of orders) [unverified].
-/

open MeasureTheory Set Function Topology NumberField IsDedekindDomain WithZero Matrix QuadFormsKB.Lattices
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Tamagawa LocalDensity QuadFormsKB.Tamagawa.BinaryCM QuadFormsKB.Tamagawa.BinaryNormOne
  QuadFormsKB.HilbertModular

section LocalMeasure

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] {D : 𝓞 F} (S : SqrtData D E)
  (k : HeightOneSpectrum (𝓞 F) → ℕ) (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

theorem algebraMap_mem_coordOrder {c : Fv} (hc : Valued.v c ≤ 1) :
    algebraMap Fv (QuadK D Fv) c ∈ coordOrder (-D) v :=
  (mem_coordOrder_iff (d := -D) v (algebraMap Fv (QuadK D Fv) c)).2 ⟨by simpa using hc, by simp⟩

/-- **The window $1+\varpi^kR_v$ in $E_v^\times$** ($R_v = \mathfrak o_v[\omega]$). -/
def winR : Subgroup (QuadK D Fv)ˣ := unitWindow (-D) v (πF v) (k v) (coordOrder (-D) v)

theorem winR_le_winO : winR k v ≤ winO S k v := by
  rintro u ⟨huR, hu'R, y, hy, hyu⟩
  exact ⟨coordOrder_le_maxOrder (sqrtBasis_zero S) (sqrtBasis_mul_self S) v huR,
    coordOrder_le_maxOrder (sqrtBasis_zero S) (sqrtBasis_mul_self S) v hu'R, y,
    coordOrder_le_maxOrder (sqrtBasis_zero S) (sqrtBasis_mul_self S) v hy, hyu⟩

include S in
/-- **The windows $1+\varpi^kR_v$ and $W_k$ (`windowZ`) agree** ($k\ge1$). -/
theorem mem_winR_iff (hk : 1 ≤ k v) (z : (QuadK D Fv)ˣ) : z ∈ winR k v ↔ z ∈ windowZ D v (k v) := by
  have hϖ0 : πF v ≠ 0 := πF_ne_zero v
  have hπk : Valued.v (πF v ^ k v) = exp (-(k v : ℤ)) := valued_πF_pow v (k v)
  constructor
  · rintro ⟨-, -, y, hy, hyu⟩
    have hre := congrArg QuadraticAlgebra.re hyu
    have him := congrArg QuadraticAlgebra.im hyu
    simp only [QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
      QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.algebraMap_re,
      QuadraticAlgebra.algebraMap_im, mul_zero, zero_mul, add_zero, sub_zero] at hre him
    obtain ⟨hyre, hyim⟩ := (mem_coordOrder_iff v y).1 hy
    refine ⟨?_, ?_⟩
    · show Valued.v ((z : QuadK D Fv).re - 1) ≤ exp (-(k v : ℤ))
      rw [hre, map_mul, hπk]
      calc exp (-(k v : ℤ)) * Valued.v y.re ≤ exp (-(k v : ℤ)) * 1 := mul_le_mul' le_rfl hyre
        _ = _ := mul_one _
    · show Valued.v (z : QuadK D Fv).im ≤ exp (-(k v : ℤ))
      rw [him, map_mul, hπk]
      calc exp (-(k v : ℤ)) * Valued.v y.im ≤ exp (-(k v : ℤ)) * 1 := mul_le_mul' le_rfl hyim
        _ = _ := mul_one _
  · rintro ⟨hre, him⟩
    set a : Fv := (πF v ^ k v)⁻¹ * ((z : QuadK D Fv).re - 1) with ha
    set b : Fv := (πF v ^ k v)⁻¹ * (z : QuadK D Fv).im with hb
    have hav : Valued.v a ≤ 1 := by
      rw [ha, map_mul, map_inv₀, hπk]
      calc (exp (-(k v : ℤ)))⁻¹ * Valued.v ((z : QuadK D Fv).re - 1) ≤ (exp (-(k v : ℤ)))⁻¹ * exp (-(k v : ℤ)) :=
            mul_le_mul' le_rfl hre
        _ = 1 := inv_mul_cancel₀ exp_ne_zero
    have hbv : Valued.v b ≤ 1 := by
      rw [hb, map_mul, map_inv₀, hπk]
      calc (exp (-(k v : ℤ)))⁻¹ * Valued.v (z : QuadK D Fv).im ≤ (exp (-(k v : ℤ)))⁻¹ * exp (-(k v : ℤ)) :=
            mul_le_mul' le_rfl him
        _ = 1 := inv_mul_cancel₀ exp_ne_zero
    set y : QuadK D Fv := ⟨a, b⟩ with hy
    have hyR : y ∈ coordOrder (-D) v := (mem_coordOrder_iff (d := -D) v y).2 ⟨hav, hbv⟩
    have hzy : (z : QuadK D Fv) - 1 = algebraMap Fv (QuadK D Fv) (πF v ^ k v) * y := by
      refine QuadraticAlgebra.ext ?_ ?_
      · simp only [QuadraticAlgebra.re_sub, QuadraticAlgebra.re_one, QuadraticAlgebra.re_mul,
          QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, mul_zero, zero_mul, add_zero]
        show _ = πF v ^ k v * a
        rw [ha, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hϖ0), one_mul]
      · simp only [QuadraticAlgebra.im_sub, QuadraticAlgebra.im_one, QuadraticAlgebra.im_mul,
          QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, mul_zero, zero_mul, add_zero, sub_zero]
        show _ = πF v ^ k v * b
        rw [hb, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hϖ0), one_mul]
    have hπR : algebraMap Fv (QuadK D Fv) (πF v ^ k v) ∈ coordOrder (-D) v := by
      refine algebraMap_mem_coordOrder v ?_
      rw [hπk, ← exp_zero]
      exact exp_le_exp.2 (by simp)
    have hz2 : (z : QuadK D Fv) = 1 + algebraMap Fv (QuadK D Fv) (πF v ^ k v) * y := by rw [← hzy]; ring
    have hzR : (z : QuadK D Fv) ∈ coordOrder (-D) v := by
      rw [hz2]
      exact (coordOrder (-D) v).add_mem (coordOrder (-D) v).one_mem ((coordOrder (-D) v).mul_mem hπR hyR)
    obtain ⟨u, hu, hue⟩ := exists_mem_unitWindow (sqrtBasis_zero S) (sqrtBasis_mul_self S) v (valued_πF v) hk
      (coordOrder_le_maxOrder (sqrtBasis_zero S) (sqrtBasis_mul_self S) v hyR)
    have huz : u = z := Units.ext (hue.trans hz2.symm)
    subst huz
    exact ⟨hzR, inv_mem_coordOrder (sqrtBasis_zero S) (sqrtBasis_mul_self S) v hu.1 hu.2.1 hzR, y, hyR, hzy⟩

include S in
/-- **A scalar of $1+\varpi^kO_{E,v}$ lies in $1+\varpi^kR_v$.** (Because $O_{E,v}\cap F_v = \mathfrak o_v$.) -/
theorem mem_winR_of_im_zero {c : (QuadK D Fv)ˣ} (hc : c ∈ winO S k v) (him : (c : QuadK D Fv).im = 0) :
    c ∈ winR k v := by
  have hϖ0 : πF v ≠ 0 := πF_ne_zero v
  obtain ⟨hcO, hc'O, y0, hy0, hyc0⟩ := hc
  set y : QuadK D Fv := y0 with hyy
  have hy : y ∈ maxOrderCM S v := hy0
  have hyc : (c : QuadK D Fv) - 1 = algebraMap Fv (QuadK D Fv) (πF v ^ k v) * y := hyc0
  have hy' := congrArg QuadraticAlgebra.im hyc
  simp only [QuadraticAlgebra.im_sub, QuadraticAlgebra.im_one, QuadraticAlgebra.im_mul,
    QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, mul_zero, zero_mul, add_zero, sub_zero] at hy'
  have hyim : y.im = 0 := by
    have : πF v ^ k v * y.im = 0 := by rw [← hy', him]
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (pow_ne_zero _ hϖ0)
    · exact h
  have hy2 : y = ⟨y.re, 0⟩ := QuadraticAlgebra.ext rfl hyim
  have hy3 := ((isMaxInt_mk_iff (d := -D) v y.re 0).1 (hy2 ▸ hy)).2
  simp only [mul_zero, sub_zero] at hy3
  have hyre : Valued.v y.re ≤ 1 := le_one_of_mul_self_le_one (by rwa [← map_mul])
  have hyR : y ∈ coordOrder (-D) v := (mem_coordOrder_iff (d := -D) v y).2 ⟨hyre, by rw [hyim, map_zero]; exact zero_le⟩
  have hπR : algebraMap Fv (QuadK D Fv) (πF v ^ k v) ∈ coordOrder (-D) v := by
    refine algebraMap_mem_coordOrder v ?_
    rw [valued_πF_pow, ← exp_zero]
    exact exp_le_exp.2 (by simp)
  have hcR : (c : QuadK D Fv) ∈ coordOrder (-D) v := by
    have : (c : QuadK D Fv) = 1 + algebraMap Fv (QuadK D Fv) (πF v ^ k v) * y := by rw [← hyc]; ring
    rw [this]
    exact (coordOrder (-D) v).add_mem (coordOrder (-D) v).one_mem ((coordOrder (-D) v).mul_mem hπR hyR)
  exact ⟨hcR, inv_mem_coordOrder (sqrtBasis_zero S) (sqrtBasis_mul_self S) v hcO hc'O hcR, y, hyR, hyc⟩

/-- **The torus image of the window**, $H_O = \mathrm{tor}(1+\varpi^kO_{E,v})$. -/
def HO : Subgroup (SOv v (diagForm1 D)) := (winO S k v).map (torSOK D Fv)

/-- **The torus image of the smaller window**, $H_R = \mathrm{tor}(1+\varpi^kR_v)$ (a congruence subgroup). -/
def HR : Subgroup (SOv v (diagForm1 D)) := (winR k v).map (torSOK D Fv)

theorem coe_HO : (HO S k v : Set (SOv v (diagForm1 D))) = Uloc S k v := rfl

theorem HR_le_HO : HR (D := D) k v ≤ HO S k v := Subgroup.map_mono (winR_le_winO S k v)

include S in
/-- **$H_R$ is the principal congruence subgroup of level $k+s$** ($|2|_v = q^{-s}$). -/
theorem coe_HR (hD : D ≠ 0) (hk : 1 ≤ k v) :
    (HR (D := D) k v : Set (SOv v (diagForm1 D))) =
      (congSubSOBin v D (k v + sExp v) (by omega) : Set (SOv v (diagForm1 D))) := by
  rw [HR, Subgroup.coe_map]
  have h1 : ((winR (D := D) k v : Subgroup (QuadK D Fv)ˣ) : Set (QuadK D Fv)ˣ) = windowZ D v (k v) :=
    Set.ext fun z => mem_winR_iff S k v hk z
  rw [h1, torSOK_image_window D v hD hk]
  rfl

include S in
/-- **The index $[H_O : H_R] = [1+\varpi^kO_{E,v} : 1+\varpi^kR_v]$** (the kernel of the torus map, the scalars,
lies in the smaller window). -/
theorem relIndex_HR_HO : (HR (D := D) k v).relIndex (HO S k v) = (winR (D := D) k v).relIndex (winO S k v) := by
  set φ := torSOK D Fv with hφ
  let ψ : winO S k v →* HO S k v := φ.subgroupMap (winO S k v)
  have hψ : Function.Surjective ψ := φ.subgroupMap_surjective _
  have hcomap : ((HR (D := D) k v).subgroupOf (HO S k v)).comap ψ = (winR (D := D) k v).subgroupOf (winO S k v) := by
    ext u
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨u', hu'R, hu'⟩
      have hker : φ ((u : (QuadK D Fv)ˣ)⁻¹ * u') = 1 := by
        rw [map_mul, map_inv]
        have : φ (u : (QuadK D Fv)ˣ) = φ u' := hu'.symm
        rw [this, inv_mul_cancel]
      have him : (((u : (QuadK D Fv)ˣ)⁻¹ * u' : (QuadK D Fv)ˣ) : QuadK D Fv).im = 0 :=
        (torSOK_eq_one_iff D Fv _).1 hker
      have hmem : (u : (QuadK D Fv)ˣ)⁻¹ * u' ∈ winO S k v :=
        (winO S k v).mul_mem ((winO S k v).inv_mem u.2) (winR_le_winO S k v hu'R)
      have hR := mem_winR_of_im_zero S k v hmem him
      have : (u : (QuadK D Fv)ˣ) = u' * ((u : (QuadK D Fv)ˣ)⁻¹ * u')⁻¹ := by group
      show (u : (QuadK D Fv)ˣ) ∈ winR k v
      rw [this]
      exact (winR k v).mul_mem hu'R ((winR k v).inv_mem hR)
    · intro h
      exact ⟨u, h, rfl⟩
  rw [Subgroup.relIndex, Subgroup.relIndex, ← hcomap, Subgroup.index_comap_of_surjective _ hψ]

include S in
theorem isOpen_Uloc (hD : D ≠ 0) (hk : 1 ≤ k v) : IsOpen (Uloc S k v) := by
  have hopen : IsOpen (HR (D := D) k v : Set (SOv v (diagForm1 D))) := by
    rw [coe_HR S k v hD hk]
    exact isOpen_congSubSO v (k v + sExp v) (by omega)
  exact Subgroup.isOpen_mono (HR_le_HO S k v) hopen

include S in
theorem measurableSet_Uloc (hD : D ≠ 0) (hk : 1 ≤ k v) : MeasurableSet (Uloc S k v) :=
  (isOpen_Uloc S k v hD hk).measurableSet

include S in
/-- **The local volume of $U_v$** (item 2, third part): $\mu^{SO}_v(U_v) = q^{c_v}\cdot q^{3s+\delta}q^{-(k+s)}$ for
$k\ge\max(1,c_v,3s+2\delta+1)$, $|2|_v = q^{-s}$, $|D|_v = q^{-\delta}$. *Proof:* $U_v = \mathrm{tor}(1+\varpi^kO_{E,v})$
contains the principal congruence subgroup $K_{k+s} = \mathrm{tor}(1+\varpi^kR_v)$ (`torSOK_image_window`) with index
$[1+\varpi^kO:1+\varpi^kR] = q^{c_v}$ (the kernel of the torus map lies in the smaller window), and
$\mu_v(K_{k+s}) = q^{3s+\delta}q^{-(k+s)}$ (`muLocSO_congSubSO`). -/
@[kb "weil1982" "Thm 2.3.1 (local ratios, finite places) [unverified]"]
theorem muLocSO_Uloc (hD : D ≠ 0) (hk1 : 1 ≤ k v) (hkc : cv S v ≤ k v)
    (hk3 : 3 * sExp v + 2 * eExp D hD v + 1 ≤ k v) :
    Measure.muLocSO v (diagForm1 D) 1 (Uloc S k v) =
      (Loc.qv v : ℝ≥0∞) ^ cv S v *
        ENNReal.ofReal ((DVR.q (v.adicCompletionIntegers F) : ℝ) ^ (3 * sExp v + eExp D hD v) *
          ((DVR.q (v.adicCompletionIntegers F) : ℝ)⁻¹) ^ (k v + sExp v)) := by
  have hle := HR_le_HO S k v
  have hopen : IsOpen (HR (D := D) k v : Set (SOv v (diagForm1 D))) := by
    rw [coe_HR S k v hD hk1]
    exact isOpen_congSubSO v (k v + sExp v) (by omega)
  have hidx : (HR (D := D) k v).relIndex (HO S k v) = Loc.qv v ^ cv S v := by
    rw [relIndex_HR_HO S k v]
    exact relIndex_unitWindow_cv S v hk1 hkc
  have hfin : (HR (D := D) k v).relIndex (HO S k v) ≠ 0 := by
    rw [hidx]; exact pow_ne_zero _ (Loc.qv_pos v).ne'
  have : (Measure.muLocSO v (diagForm1 D) 1).IsMulLeftInvariant := by unfold Measure.muLocSO; infer_instance
  have e := measure_subgroup_eq_relIndex_mul (Measure.muLocSO v (diagForm1 D) 1) hopen hle hfin
  rw [← coe_HO S k v, e, hidx, coe_HR S k v hD hk1,
    muLocSO_congSubSO v hD (valued_two_eq v) (valued_eExp D hD v) (by omega)]
  rw [Nat.cast_pow]

end LocalMeasure

/-! ### Good places: $\alpha_v = \lambda_v$ -/

section Good

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] {D : 𝓞 F} (S : SqrtData D E) (v : HeightOneSpectrum (𝓞 F))

include S in
/-- **The combinatorial character is $\chi_E$ at every place with $2D\notin\mathfrak p_v$**
(not only almost everywhere): both are the residue symbol
$\bigl(\tfrac{-4D}{\mathfrak p}\bigr)$ (`chiP_binary_eq_charNF`, `relChar_eq_charNF` with $\theta = 2\sqrt{-D}$). -/
theorem chiP_eq_chiE_of_not_mem (hv : (2 * D : 𝓞 F) ∉ v.asIdeal) : chiP v (diagForm1 D) = chiE F E v := by
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := fun h => hv (v.asIdeal.mul_mem_right _ h)
  have hD : D ∉ v.asIdeal := fun h => hv (v.asIdeal.mul_mem_left _ h)
  have h4 : (4 : 𝓞 F) ∉ v.asIdeal := fun h =>
    h2 (v.isPrime.mem_of_pow_mem 2 (by simpa [show (4 : 𝓞 F) = 2 ^ 2 by norm_num] using h))
  have hdet : (diagForm1 D).hessian.det ∉ v.asIdeal := by
    rw [hessian_det_diagForm1]
    exact fun h => (v.isPrime.mem_or_mem h).elim h4 hD
  have hdet' : (-(diagForm1 D).hessian.det) ∉ v.asIdeal := fun h => hdet (v.asIdeal.neg_mem_iff.1 h)
  rw [chiP_binary_eq_charNF v (diagForm1 D) h2 hdet]
  have hθ2 : (2 * S.θ) ^ 2 = algebraMap F E (algebraMap (𝓞 F) F (-(diagForm1 D).hessian.det)) := by
    rw [mul_pow, S.sq, hessian_det_diagForm1]
    simp only [map_neg, map_mul, map_ofNat]
    ring
  have hθc : Binary.Rel.conj F E (2 * S.θ) = -(2 * S.θ) := by
    rw [map_mul, S.conj_eq, map_ofNat]; ring
  have hint : IsIntegral ℤ (2 * S.θ) :=
    IsIntegral.of_pow two_pos (by rw [hθ2]; exact (RingOfIntegers.isIntegral_coe _).algebraMap)
  set θO : 𝓞 E := ⟨2 * S.θ, hint⟩ with hθOdef
  have hθO : Binary.Rel.conjO F E θO = -θO := by
    apply RingOfIntegers.coe_injective
    rw [Binary.Rel.algebraMap_conjO]
    exact hθc
  have hδO : algebraMap (𝓞 F) (𝓞 E) (-(diagForm1 D).hessian.det) = θO ^ 2 := by
    apply RingOfIntegers.coe_injective
    show algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) _) = algebraMap (𝓞 E) E (θO ^ 2)
    rw [map_pow, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E]
    exact hθ2.symm
  unfold chiE
  rw [Binary.Rel.relChar_eq_charNF hθO hδO h2 hdet']

include S in
/-- **$\alpha_v = \lambda_v$ at the good places:** for $2D\notin\mathfrak p_v$,
$\alpha_v(L,L)\cdot(1-\chi_E(v)/N\mathfrak p)^{-1} = 1$. -/
theorem siegelDensity_mul_lamL (hD : D ≠ 0) (hv : (2 * D : 𝓞 F) ∉ v.asIdeal) :
    NF.siegelDensity v (diagForm1 D) (diagForm1 D) * (1 - chiE F E v / (Ideal.absNorm v.asIdeal : ℝ)) ^ (-1 : ℤ) = 1 := by
  have hQ : (diagForm1 D).Nondegenerate := nondegenerate_diagForm1 hD
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := fun h => hv (v.asIdeal.mul_mem_right _ h)
  have hD' : D ∉ v.asIdeal := fun h => hv (v.asIdeal.mul_mem_left _ h)
  have h4 : (4 : 𝓞 F) ∉ v.asIdeal := fun h =>
    h2 (v.isPrime.mem_of_pow_mem 2 (by simpa [show (4 : 𝓞 F) = 2 ^ 2 by norm_num] using h))
  have hbad : v ∉ badPrimes (diagForm1 D) := by
    intro h
    change 2 * (diagForm1 D).hessian.det ∈ v.asIdeal at h
    rw [hessian_det_diagForm1] at h
    rcases v.isPrime.mem_or_mem h with h | h
    · exact h2 h
    · exact (v.isPrime.mem_or_mem h).elim h4 hD'
  rw [siegelDensity_binary_good (diagForm1 D) hQ v hbad, chiP_eq_chiE_of_not_mem S v hv, _root_.zpow_neg_one]
  have hdeg : Module.finrank F E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two F E
  exact mul_inv_cancel₀ (lamL_pos (abs_chiE_le hdeg) v).ne'

end Good

/-! ### The measure of $K'$ -/

section KMeasure

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] {D : 𝓞 F} (S : SqrtData D E)
  (Sfin : Finset (HeightOneSpectrum (𝓞 F))) (k : HeightOneSpectrum (𝓞 F) → ℕ)

/-- $N\mathfrak p_v$ as a real number. -/
abbrev qn (v : HeightOneSpectrum (𝓞 F)) : ℝ := (Ideal.absNorm v.asIdeal : ℝ)

theorem qn_pos (v : HeightOneSpectrum (𝓞 F)) : 0 < qn v := by
  have := Loc.qv_pos v
  exact_mod_cast this

/-- **The local volume of $U_v$ relative to $SO(L_v)$**:
$q^{c_v}\cdot q^{3s+\delta}q^{-(k+s)}$ ($c_v$ = `cv`, $s = $ `sExp`, $\delta$ = `eExp D`). -/
def Aloc (hD : D ≠ 0) (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  qn v ^ cv S v * (qn v ^ (3 * sExp v + eExp D hD v) * (qn v)⁻¹ ^ (k v + sExp v))

theorem Aloc_pos (hD : D ≠ 0) (v : HeightOneSpectrum (𝓞 F)) : 0 < Aloc S k hD v := by
  have := qn_pos v
  unfold Aloc
  positivity

/-- **The Haar measure of $U_v$** (normalized by $SO(L_v)$): $\mathrm{haar}_v(U_v) = A_v/\alpha_v$. -/
theorem haarSO_Uloc (hD : D ≠ 0) (v : HeightOneSpectrum (𝓞 F)) (hk1 : 1 ≤ k v) (hkc : cv S v ≤ k v)
    (hk3 : 3 * sExp v + 2 * eExp D hD v + 1 ≤ k v) :
    haarSO (diagForm1 D) v (Uloc S k v) =
      ENNReal.ofReal (Aloc S k hD v / NF.siegelDensity v (diagForm1 D) (diagForm1 D)) := by
  have hQ : (diagForm1 D).Nondegenerate := nondegenerate_diagForm1 hD
  have hα := siegelDensity_self_pos' (diagForm1 D) hQ v
  have hq : (DVR.q (v.adicCompletionIntegers F) : ℝ) = qn v := by
    rw [NF.q_completion]
  have hq' : (Loc.qv v : ℝ≥0∞) = ENNReal.ofReal (qn v) := by
    rw [qn, ← ENNReal.ofReal_natCast]
  rw [haarSO_eq_div (diagForm1 D) hQ v one_pos, muLocSO_Uloc S k v hD hk1 hkc hk3, muLocSO_soStabSO, div_one,
    hq, hq', ← ENNReal.ofReal_pow (qn_pos v).le, ← ENNReal.ofReal_mul (pow_nonneg (qn_pos v).le _),
    ← ENNReal.ofReal_div_of_pos hα]
  rfl

/-- **The measure of $K'$** (item 2, third part): with $\lambda_v = 1-\chi_E(v)/N\mathfrak p_v$,
$$\mu_f^\lambda(K') = \prod_{v\in S}q^{c_v}\cdot q^{3s+\delta}q^{-(k+s)}\cdot(1-\chi_E(v)/N\mathfrak p_v)^{-1}.$$
(Good places contribute $1$: $\alpha_v = \lambda_v$ there.) -/
@[kb "weil1982" "Thm 2.3.1 (local ratios, finite places) [unverified]"]
theorem muFin_Kp (hD : D ≠ 0) (hk1 : ∀ v ∈ Sfin, 1 ≤ k v) (hkc : ∀ v ∈ Sfin, cv S v ≤ k v)
    (hk3 : ∀ v ∈ Sfin, 3 * sExp v + 2 * eExp D hD v + 1 ≤ k v)
    (hS : ∀ v ∉ Sfin, (2 * D : 𝓞 F) ∉ v.asIdeal) :
    Measure.muFin (diagForm1 D) (lamL (chiE F E)) (Kp S Sfin k) =
      ENNReal.ofReal (∏ v ∈ Sfin, Aloc S k hD v * (1 - chiE F E v / qn v)⁻¹) := by
  classical
  have hdeg : Module.finrank F E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two F E
  have hQ : (diagForm1 D).Nondegenerate := nondegenerate_diagForm1 hD
  have hχ : ∀ v, |chiE F E v| ≤ 1 := abs_chiE_le hdeg
  have hα : ∀ v, 0 < NF.siegelDensity v (diagForm1 D) (diagForm1 D) := siegelDensity_self_pos' (diagForm1 D) hQ
  have hlam : ∀ v, 0 < 1 - chiE F E v / qn v := fun v => lamL_pos hχ v
  have hhaar : ∀ v ∈ Sfin, haarSO (diagForm1 D) v (Uloc S k v) =
      ENNReal.ofReal (Aloc S k hD v / NF.siegelDensity v (diagForm1 D) (diagForm1 D)) := fun v hv =>
    haarSO_Uloc S k hD v (hk1 v hv) (hkc v hv) (hk3 v hv)
  rw [Kp, muFin_boxSO_haar_of_ne_top (diagForm1 D) (lamL (chiE F E)) Sfin (Uloc S k)
    (fun v hv => measurableSet_Uloc S k v hD (hk1 v hv))
    (fun v hv => by rw [hhaar v hv]; exact ENNReal.ofReal_ne_top),
    finFactor_lamL_eq (diagForm1 D) hQ hχ,
    tprod_eq_prod (s := Sfin) (fun v hv => siegelDensity_mul_lamL S v hD (hS v hv)),
    Finset.prod_congr rfl hhaar, ← ENNReal.ofReal_prod_of_nonneg (fun v _ => div_nonneg (Aloc_pos S k hD v).le (hα v).le),
    ← ENNReal.ofReal_mul (Finset.prod_nonneg fun v _ => by
      rw [_root_.zpow_neg_one]; exact mul_nonneg (hα v).le (inv_nonneg.2 (hlam v).le))]
  congr 1
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [_root_.zpow_neg_one]
  have := (hα v).ne'
  field_simp

end KMeasure

/-! ### The measures of the idele boxes $N_F$ and $A_f$ -/

section Boxes

theorem measurableSet_oneAdd {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) (m : ℕ) :
    MeasurableSet {r : (w.adicCompletion L)ˣ | Valued.v ((r : w.adicCompletion L) - 1) ≤ exp (-(m : ℤ))} := by
  have hA : {r : (w.adicCompletion L)ˣ | Valued.v ((r : w.adicCompletion L) - 1) ≤ exp (-(m : ℤ))} =
      Units.val ⁻¹' ((fun x => x - 1) ⁻¹' (Analysis.latticeV w (m : ℤ) : Set (w.adicCompletion L))) := by
    ext r; simp [Analysis.mem_latticeV]
  rw [hA]
  exact ((Analysis.measurableSet_latticeV w _).preimage (measurable_id.sub_const 1)).preimage
    Units.continuous_val.measurable

theorem oneAdd_subset_units {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) {m : ℕ} (hm : 1 ≤ m) :
    {r : (w.adicCompletion L)ˣ | Valued.v ((r : w.adicCompletion L) - 1) ≤ exp (-(m : ℤ))} ⊆ unitsVSub w :=
  fun _ hu => valued_eq_one_of_sub_one_lt w (valued_lt_one_of_le_exp w hm hu)

/-- **The measure of an idele box with windows inside the units**: $\mu_f(\mathrm{box}(T,U)) = |d_L|^{-1/2}\prod_{w\in T}
\omega_w(U_w)/\omega_w(\mathcal O_w^\times)$, as an `ofReal`. -/
theorem muFinUnits_ideleBox_ofReal {L : Type} [Field L] [NumberField L] (T : Finset (HeightOneSpectrum (𝓞 L)))
    (U : ∀ w : HeightOneSpectrum (𝓞 L), Set (w.adicCompletion L)ˣ) (hU : ∀ w ∈ T, MeasurableSet (U w))
    (hsub : ∀ w ∈ T, U w ⊆ unitsVSub w) :
    muFinUnits L (ideleBox T U) =
      ENNReal.ofReal (ohatVol L * ∏ w ∈ T, (omegaV w (U w)).toReal / (omegaV w (unitsVSub w)).toReal) := by
  rw [muFinUnits_ideleBox_of_measurable T U hU, muFinUnits_OHatUnits]
  have h1 : ∀ w ∈ T, omegaV w (U w) / omegaV w (unitsVSub w) =
      ENNReal.ofReal ((omegaV w (U w)).toReal / (omegaV w (unitsVSub w)).toReal) := by
    intro w hw
    have hfin : omegaV w (U w) ≠ ⊤ := ne_top_of_le_ne_top (omegaV_unitsVSub_ne_top w) (measure_mono (hsub w hw))
    rw [ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos (omegaV_unitsVSub_ne_zero w) (omegaV_unitsVSub_ne_top w)),
      ENNReal.ofReal_toReal hfin, ENNReal.ofReal_toReal (omegaV_unitsVSub_ne_top w)]
  rw [Finset.prod_congr rfl h1, ← ENNReal.ofReal_prod_of_nonneg
    (fun w _ => div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg), ← ENNReal.ofReal_mul ohatVol_pos.le]

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] {D : 𝓞 F} (S : SqrtData D E)
  (Sfin : Finset (HeightOneSpectrum (𝓞 F))) (k : HeightOneSpectrum (𝓞 F) → ℕ)

/-- **The measure of $N_F$** (item 2, second part):
$\mu_{f,F}(N_F) = |d_F|^{-1/2}\prod_{v\in S}q^{-k_v}(1-q^{-1})^{-1}$. -/
@[kb "weil1982" "Thm 2.3.1 (local ratios, finite places) [unverified]"]
theorem muFinUnits_boxF (hk : ∀ v ∈ Sfin, 1 ≤ k v) :
    muFinUnits F (boxF Sfin k) = ENNReal.ofReal (ohatVol F *
      ∏ v ∈ Sfin, (Ideal.absNorm v.asIdeal : ℝ)⁻¹ ^ k v * (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹)⁻¹) := by
  rw [boxF, muFinUnits_ideleBox_ofReal Sfin (winF k) (fun v _ => measurableSet_oneAdd v (k v))
    (fun v hv => oneAdd_subset_units v (hk v hv))]
  congr 2
  exact Finset.prod_congr rfl fun v hv => omegaV_window_ratio v (hk v hv)

/-- The window at $w$ in the form $\{r : v_w(r-1)\le q_w^{-e_wk}\}$ ($e_w$ = `ramE`). -/
theorem winE_eq (w : HeightOneSpectrum (𝓞 E)) :
    winE E k w = {r : (w.adicCompletion E)ˣ | Valued.v ((r : w.adicCompletion E) - 1) ≤
      exp (-((ramE (underPlace (k := F) w) w * k (underPlace (k := F) w) : ℕ) : ℤ))} := by
  unfold winE
  have : Valued.v (localRingHom (underPlace (k := F) w) w rfl (πF (underPlace (k := F) w))) ^
      k (underPlace (k := F) w) =
      exp (-((ramE (underPlace (k := F) w) w * k (underPlace (k := F) w) : ℕ) : ℤ)) := by
    rw [valued_localRingHom_exp (underPlace (k := F) w) w rfl (valued_πF _), ← WithZero.exp_nsmul]
    congr 1
    simp only [nsmul_eq_mul, Nat.cast_mul]
    ring
  rw [this]

theorem one_le_ramE_mul (hk : ∀ v ∈ Sfin, 1 ≤ k v) {w : HeightOneSpectrum (𝓞 E)}
    (hw : w ∈ nsBadK (K := E) Sfin) :
    1 ≤ ramE (underPlace (k := F) w) w * k (underPlace (k := F) w) :=
  Nat.mul_pos (one_le_ramE _ w rfl) (hk _ (mem_nsBadK.1 hw))

include S in
/-- **The local ratio over $v$**: $\prod_{w\mid v}\omega_w(1+\varpi^k\mathcal O_w)/\omega_w(\mathcal O_w^\times) =
q^{-2k}(1-q^{-1})^{-1}(1-\chi_E(v)q^{-1})^{-1}$. -/
theorem prod_winE_ratio (hk : ∀ v ∈ Sfin, 1 ≤ k v) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∈ Sfin) :
    ∏ w ∈ placesOver (K := E) v, (omegaV w (winE E k w)).toReal / (omegaV w (unitsVSub w)).toReal =
      (Ideal.absNorm v.asIdeal : ℝ)⁻¹ ^ (2 * k v) * (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹)⁻¹ *
        (1 - (Binary.Rel.relChar E v : ℝ) * (Ideal.absNorm v.asIdeal : ℝ)⁻¹)⁻¹ := by
  rw [← prod_placeSet_eq v (fun w => (omegaV w (winE E k w)).toReal / (omegaV w (unitsVSub w)).toReal),
    ← prod_omegaV_window_ratio (sqrtBasis_zero S) (sqrtBasis_mul_self S) v (valued_πF v) (hk v hv)]
  refine Finset.prod_congr rfl fun w _ => ?_
  obtain ⟨w, hw⟩ := w
  subst hw
  rfl

include S in
/-- **The measure of $A_f$** (item 2, first part): $\mu_{f,E}(A_f) = |d_E|^{-1/2}\prod_{v\in S}
q^{-2k_v}(1-q^{-1})^{-1}(1-\chi_E(v)q^{-1})^{-1}$. -/
@[kb "weil1982" "Thm 2.3.1 (local ratios, finite places) [unverified]"]
theorem muFinUnits_boxE (hk : ∀ v ∈ Sfin, 1 ≤ k v) :
    muFinUnits E (boxE E Sfin k) = ENNReal.ofReal (ohatVol E *
      ∏ v ∈ Sfin, ((Ideal.absNorm v.asIdeal : ℝ)⁻¹ ^ (2 * k v) * (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹)⁻¹ *
        (1 - (Binary.Rel.relChar E v : ℝ) * (Ideal.absNorm v.asIdeal : ℝ)⁻¹)⁻¹)) := by
  classical
  have hreg : ∀ f : HeightOneSpectrum (𝓞 E) → ℝ, ∏ w ∈ nsBadK (K := E) Sfin, f w =
      ∏ v ∈ Sfin, ∏ w ∈ placesOver (K := E) v, f w := fun f => Finset.prod_biUnion (pairwiseDisjoint_placesOver Sfin)
  rw [boxE, muFinUnits_ideleBox_ofReal (nsBadK (K := E) Sfin) (winE E k)
    (fun w hw => by rw [winE_eq]; exact measurableSet_oneAdd w _)
    (fun w hw => by rw [winE_eq]; exact oneAdd_subset_units w (one_le_ramE_mul Sfin k hk hw)),
    hreg (fun w => (omegaV w (winE E k w)).toReal / (omegaV w (unitsVSub w)).toReal)]
  congr 2
  exact Finset.prod_congr rfl fun v hv => prod_winE_ratio S Sfin k hk v hv

end Boxes

/-! ### The finite ratio -/

section Ratio

/-- **The finite comparison constant** $|N_{F/\mathbb Q}(4d)|^{-3/2}|d_F|^{-1/2}$ ($d = -D$): the inverse of `shellRatio`. -/
def finRatio {F : Type} [Field F] [NumberField F] (D : 𝓞 F) : ℝ :=
  (((|Algebra.norm ℚ (4 * dD D)| : ℚ) : ℝ) ^ ((3 : ℝ) / 2) * |(discr F : ℝ)| ^ ((1 : ℝ) / 2))⁻¹

theorem local_identity (q χ : ℝ) (c s δ k : ℕ) :
    ((q⁻¹ ^ k * (1 - q⁻¹)⁻¹) * (q ^ c * (q ^ (3 * s + δ) * q⁻¹ ^ (k + s)) * (1 - χ / q)⁻¹)) =
      ((q⁻¹ ^ (2 * k) * (1 - q⁻¹)⁻¹ * (1 - χ * q⁻¹)⁻¹) * (q ^ c * (q ^ s) ^ 2 * q ^ δ)) := by
  by_cases hq0 : q = 0
  · subst hq0
    cases k <;> cases s <;> simp
  rw [div_eq_mul_inv]
  have e : q ^ (3 * s + δ) * q⁻¹ ^ (k + s) * q⁻¹ ^ k = q⁻¹ ^ (2 * k) * (q ^ s) ^ 2 * q ^ δ := by
    rw [inv_pow, inv_pow, inv_pow]
    field_simp
    ring
  calc _ = q ^ c * (q ^ (3 * s + δ) * q⁻¹ ^ (k + s) * q⁻¹ ^ k) * ((1 - q⁻¹)⁻¹ * (1 - χ * q⁻¹)⁻¹) := by ring
    _ = _ := by rw [e]; ring

theorem key_real {a b P X : ℝ} (ha : 0 < a) (hb : 0 < b) (hP : 0 < P) (hX : 0 < X)
    (h : a * P ^ 2 = X * b ^ 2) :
    (Real.sqrt a)⁻¹ = (X ^ ((3 : ℝ) / 2) * b ^ ((1 : ℝ) / 2))⁻¹ * (Real.sqrt b)⁻¹ * (P * X) := by
  have h1 : Real.sqrt X * b = P * Real.sqrt a := by
    have : Real.sqrt X * Real.sqrt (b ^ 2) = Real.sqrt a * Real.sqrt (P ^ 2) := by
      rw [← Real.sqrt_mul hX.le, ← Real.sqrt_mul ha.le, h]
    rwa [Real.sqrt_sq hb.le, Real.sqrt_sq hP.le, mul_comm (Real.sqrt a)] at this
  have e3 : X ^ ((3 : ℝ) / 2) = X * Real.sqrt X := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hX, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have e1 : b ^ ((1 : ℝ) / 2) = Real.sqrt b := by rw [Real.sqrt_eq_rpow]
  rw [e3, e1]
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hsX : 0 < Real.sqrt X := Real.sqrt_pos.2 hX
  have hbb : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb.le
  field_simp
  nlinarith [h1, hbb]

variable {F : Type} [Field F] [NumberField F]

/-- **The product formula in exponent form:** if $|x|_v = q_v^{-e_v}$ for all $v$ and $e_v = 0$ off $S$, then
$\prod_{v\in S}N\mathfrak p_v^{e_v} = |N_{F/\mathbb Q}x|$ (`finprod_norm_eq_inv_real_complex`). -/
theorem prod_qn_pow_eq (Sfin : Finset (HeightOneSpectrum (𝓞 F))) (x : F) (hx : x ≠ 0)
    (e : HeightOneSpectrum (𝓞 F) → ℕ)
    (he : ∀ v, Valued.v (algebraMap F (v.adicCompletion F) x) = exp (-(e v : ℤ)))
    (hoff : ∀ v ∉ Sfin, e v = 0) :
    ∏ v ∈ Sfin, (Ideal.absNorm v.asIdeal : ℝ) ^ e v = ((|Algebra.norm ℚ x| : ℚ) : ℝ) := by
  classical
  have h1 := finprod_norm_eq_inv_real_complex x hx
  rw [← norm_mixedEmbedding_eq_real_complex, NumberField.mixedEmbedding.norm_eq_norm] at h1
  have h2 : ∀ v : HeightOneSpectrum (𝓞 F),
      ‖algebraMap F (v.adicCompletion F) x‖ = ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ e v := by
    intro v
    rw [norm_of_valued_exp_binary v (he v), NF.q_completion]
  rw [finprod_congr h2, finprod_eq_prod_of_mulSupport_subset _ (s := Sfin)] at h1
  · rw [Finset.prod_congr rfl (fun v _ => inv_pow _ _), Finset.prod_inv_distrib] at h1
    exact inv_injective h1
  · intro v hv
    by_contra h
    apply hv
    show ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ e v = 1
    rw [hoff v h, pow_zero]

theorem abs_norm_two :
    ((|Algebra.norm ℚ (2 : F)| : ℚ) : ℝ) = 2 ^ Module.finrank ℚ F := by
  have : (2 : F) = algebraMap ℚ F 2 := by simp
  rw [this, Algebra.norm_algebraMap, abs_pow, abs_of_pos (by norm_num : (0 : ℚ) < 2)]
  norm_num

/-- $|N_{F/\mathbb Q}(4\cdot(-D))| = 4^{[F:\mathbb Q]}|N_{F/\mathbb Q}D|$. -/
theorem abs_norm_four_dD (D : 𝓞 F) :
    ((|Algebra.norm ℚ (4 * dD D)| : ℚ) : ℝ) = 4 ^ Module.finrank ℚ F * |(Algebra.norm ℚ (algebraMap (𝓞 F) F D) : ℝ)| := by
  have h4 : Algebra.norm ℚ (4 : F) = 4 ^ Module.finrank ℚ F := by
    have : (4 : F) = algebraMap ℚ F 4 := by simp
    rw [this, Algebra.norm_algebraMap]
  have hneg : Algebra.norm ℚ (dD D) = (-1) ^ Module.finrank ℚ F * Algebra.norm ℚ (algebraMap (𝓞 F) F D) := by
    have : dD D = algebraMap ℚ F (-1) * algebraMap (𝓞 F) F D := by simp [dD]
    rw [this, map_mul, Algebra.norm_algebraMap]
  rw [map_mul, h4, hneg]
  push_cast
  rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  norm_num

variable {E : Type} [Field E] [NumberField E] [Algebra F E] [Algebra.IsQuadraticExtension F E] {D : 𝓞 F}
  (S : SqrtData D E) (Sfin : Finset (HeightOneSpectrum (𝓞 F))) (k : HeightOneSpectrum (𝓞 F) → ℕ)

include S in
/-- **The finite ratio, as an identity of real numbers**:
$$|d_E|^{-1/2}\prod_{v\in S}E_v = |N_{F/\mathbb Q}(4d)|^{-3/2}|d_F|^{-1/2}\cdot\bigl(|d_F|^{-1/2}\prod_{v\in S}F_v\bigr)\prod_{v\in S}K_v,$$
with $E_v = q^{-2k}(1-q^{-1})^{-1}(1-\chi q^{-1})^{-1}$, $F_v = q^{-k}(1-q^{-1})^{-1}$, $K_v = q^{c_v}q^{3s+\delta}q^{-(k+s)}
(1-\chi/q)^{-1}$. *Proof:* $F_vK_v = E_v\,q^{c_v}q^{2s_v+\delta_v}$; the product formula gives
$\prod_vq^{s_v} = 2^{[F:\mathbb Q]}$ and $\prod_vq^{\delta_v} = |N_{F/\mathbb Q}D|$; `discr_mul_prod_localIndex_sq` gives
$|d_E|(\prod_vq^{c_v})^2 = 4^{[F:\mathbb Q]}|d_F|^2|N_{F/\mathbb Q}D|$. -/
theorem finite_ratio_real (hD : D ≠ 0) (hS : ∀ v ∉ Sfin, (2 * D : 𝓞 F) ∉ v.asIdeal) :
    ohatVol E * ∏ v ∈ Sfin, ((qn v)⁻¹ ^ (2 * k v) * (1 - (qn v)⁻¹)⁻¹ *
        (1 - (Binary.Rel.relChar E v : ℝ) * (qn v)⁻¹)⁻¹) =
      finRatio D * ((ohatVol F * ∏ v ∈ Sfin, (qn v)⁻¹ ^ k v * (1 - (qn v)⁻¹)⁻¹) *
        ∏ v ∈ Sfin, Aloc S k hD v * (1 - chiE F E v / qn v)⁻¹) := by
  classical
  set n := Module.finrank ℚ F with hn
  have hD' : (algebraMap (𝓞 F) F D) ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hD
  -- Step A: the local identity
  have hA : (∏ v ∈ Sfin, (qn v)⁻¹ ^ k v * (1 - (qn v)⁻¹)⁻¹) * ∏ v ∈ Sfin, Aloc S k hD v * (1 - chiE F E v / qn v)⁻¹ =
      (∏ v ∈ Sfin, ((qn v)⁻¹ ^ (2 * k v) * (1 - (qn v)⁻¹)⁻¹ *
        (1 - (Binary.Rel.relChar E v : ℝ) * (qn v)⁻¹)⁻¹)) *
        ∏ v ∈ Sfin, (qn v ^ cv S v * (qn v ^ sExp v) ^ 2 * qn v ^ eExp D hD v) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v _ => local_identity (qn v) (chiE F E v) (cv S v) (sExp v) (eExp D hD v) (k v)
  -- Step B: the product formulas
  have hQ2 : ∏ v ∈ Sfin, qn v ^ sExp v = 2 ^ n := by
    have := prod_qn_pow_eq Sfin (2 : F) two_ne_zero (fun v => sExp v)
      (fun v => by rw [map_ofNat]; exact valued_two_eq v)
      (fun v hv => by
        have h2 := (valued_two_D_eq_one v (hS v hv)).1
        rw [valued_two_eq v, ← WithZero.exp_zero, WithZero.exp_inj] at h2
        omega)
    rw [abs_norm_two] at this
    exact this
  have hQD : ∏ v ∈ Sfin, qn v ^ eExp D hD v = |(Algebra.norm ℚ (algebraMap (𝓞 F) F D) : ℝ)| := by
    have := prod_qn_pow_eq Sfin (algebraMap (𝓞 F) F D) hD' (fun v => eExp D hD v)
      (fun v => valued_eExp D hD v)
      (fun v hv => by
        have h2 := (valued_two_D_eq_one v (hS v hv)).2
        have h3 := valued_eExp D hD v
        change Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F D)) = 1 at h2
        rw [h2, ← WithZero.exp_zero, WithZero.exp_inj] at h3
        omega)
    rw [this, Rat.cast_abs]
  have hPc : ∏ v ∈ Sfin, qn v ^ cv S v = ((∏ v ∈ Sfin, localIndex S v : ℕ) : ℝ) := by
    push_cast
    exact Finset.prod_congr rfl fun v _ => by rw [localIndex_eq]; push_cast; rfl
  have hM : ∏ v ∈ Sfin, (qn v ^ cv S v * (qn v ^ sExp v) ^ 2 * qn v ^ eExp D hD v) =
      ((∏ v ∈ Sfin, localIndex S v : ℕ) : ℝ) * (4 ^ n * |(Algebra.norm ℚ (algebraMap (𝓞 F) F D) : ℝ)|) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow, hQ2, hQD, hPc]
    rw [← pow_mul, mul_comm n 2, pow_mul]
    norm_num
    ring
  -- Step C: the discriminant relation and the real identity
  have hdisc := discr_mul_prod_localIndex_sq S hS
  set P : ℝ := ((∏ v ∈ Sfin, localIndex S v : ℕ) : ℝ) with hP
  have hNpos : 0 < |(Algebra.norm ℚ (algebraMap (𝓞 F) F D) : ℝ)| := by
    refine abs_pos.2 ?_
    have : Algebra.norm ℚ (algebraMap (𝓞 F) F D) ≠ 0 := Algebra.norm_ne_zero_iff.2 hD'
    exact_mod_cast this
  have hPpos : 0 < P := by
    rw [← hPc]
    exact Finset.prod_pos fun v _ => pow_pos (qn_pos v) _
  have haE : 0 < |(discr E : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero (K := E))
  have haF : 0 < |(discr F : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero (K := F))
  have hX : (0 : ℝ) < 4 ^ n * |(Algebra.norm ℚ (algebraMap (𝓞 F) F D) : ℝ)| := by positivity
  have key := key_real haE haF hPpos hX (by rw [hdisc]; ring)
  rw [show (ohatVol F * ∏ v ∈ Sfin, (qn v)⁻¹ ^ k v * (1 - (qn v)⁻¹)⁻¹) *
      ∏ v ∈ Sfin, Aloc S k hD v * (1 - chiE F E v / qn v)⁻¹ =
      ohatVol F * ((∏ v ∈ Sfin, (qn v)⁻¹ ^ k v * (1 - (qn v)⁻¹)⁻¹) *
        ∏ v ∈ Sfin, Aloc S k hD v * (1 - chiE F E v / qn v)⁻¹) by ring, hA, hM, finRatio, abs_norm_four_dD]
  simp only [ohatVol]
  rw [key]
  ring

theorem one_sub_inv_qn_pos (v : HeightOneSpectrum (𝓞 F)) : 0 < 1 - (qn v)⁻¹ :=
  sub_pos.2 (inv_lt_one_of_one_lt₀ (one_lt_absNorm v))

theorem prod_boxF_pos (Sfin : Finset (HeightOneSpectrum (𝓞 F))) (k : HeightOneSpectrum (𝓞 F) → ℕ) :
    0 < ohatVol F * ∏ v ∈ Sfin, (qn v)⁻¹ ^ k v * (1 - (qn v)⁻¹)⁻¹ := by
  refine mul_pos ohatVol_pos (Finset.prod_pos fun v _ => ?_)
  have := qn_pos v
  have := one_sub_inv_qn_pos v
  positivity

include S in
theorem prod_Kp_pos (hD : D ≠ 0) :
    0 < ∏ v ∈ Sfin, Aloc S k hD v * (1 - chiE F E v / qn v)⁻¹ := by
  have hdeg : Module.finrank F E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two F E
  refine Finset.prod_pos fun v _ => mul_pos (Aloc_pos S k hD v) (inv_pos.2 ?_)
  exact lamL_pos (abs_chiE_le hdeg) v

include S in
/-- **The finite ratio**: $\mu_{f,E}(A_f) = |N_{F/\mathbb Q}(4d)|^{-3/2}|d_F|^{-1/2}\cdot\mu_{f,F}(N_F)\cdot\mu^\lambda_f(K')$,
$\mu^\lambda_f$ = `muFin (diagForm1 D) (lamL (chiE F E))`. -/
@[kb "weil1982" "Thm 2.3.1 (local ratios, finite places) [unverified]"]
theorem finite_ratio (hD : D ≠ 0) (hk1 : ∀ v ∈ Sfin, 1 ≤ k v) (hkc : ∀ v ∈ Sfin, cv S v ≤ k v)
    (hk3 : ∀ v ∈ Sfin, 3 * sExp v + 2 * eExp D hD v + 1 ≤ k v)
    (hS : ∀ v ∉ Sfin, (2 * D : 𝓞 F) ∉ v.asIdeal) :
    muFinUnits E (boxE E Sfin k) = ENNReal.ofReal (finRatio D) *
      (muFinUnits F (boxF Sfin k) * Measure.muFin (diagForm1 D) (lamL (chiE F E)) (Kp S Sfin k)) := by
  have hF := prod_boxF_pos Sfin k
  have hK := prod_Kp_pos S Sfin k hD
  have hfr : 0 ≤ finRatio D := by
    unfold finRatio
    exact inv_nonneg.2 (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (abs_nonneg _) _))
  rw [muFinUnits_boxE S Sfin k hk1, muFinUnits_boxF Sfin k hk1, muFin_Kp S Sfin k hD hk1 hkc hk3 hS,
    ← ENNReal.ofReal_mul hF.le, ← ENNReal.ofReal_mul hfr]
  congr 1
  exact finite_ratio_real S Sfin k hD hS

end Ratio

/-! ### The packaged finite factor -/

section Package

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] {D : 𝓞 F}

/-- Only finitely many places $v$ have $2D\in\mathfrak p_v$. -/
theorem finite_bad_places (hD : D ≠ 0) : {v : HeightOneSpectrum (𝓞 F) | (2 * D : 𝓞 F) ∈ v.asIdeal}.Finite := by
  have hne : (2 * D : 𝓞 F) ≠ 0 := mul_ne_zero two_ne_zero hD
  refine (Ideal.finite_factors (I := Ideal.span {2 * D}) (by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hne)).subset (fun v hv => ?_)
  show v.asIdeal ∣ Ideal.span {2 * D}
  rw [Ideal.dvd_span_singleton]
  exact hv

variable (S : SqrtData D E)

/-- **The levels $k_v = \max(1,c_v,3s_v+2\delta_v+1)$** of the windows. -/
def levels (hD : D ≠ 0) (v : HeightOneSpectrum (𝓞 F)) : ℕ :=
  max (max 1 (cv S v)) (3 * sExp v + 2 * eExp D hD v + 1)

/-- **The finite factor of the measure comparison** (items 1–4), for the basis $(1,\theta)$: there are a box $A_f$ of
$\mathbb A_{E,f}^\times$, a constant $N$ and a measurable $K'\subseteq SO(V)(\mathbb A_f)$ with
$K_f = N\mathbf 1_{K'}$, $\mu_{f,E}(A_f) = \text{finRatio}\cdot N\mu^\lambda_f(K')$ and $0<N\mu^\lambda_f(K')<\infty$.
Here $A_f$ = `boxE`, $N = \mu_{f,F}(N_F)$, $K'$ = `Kp`, at the places $S = \{v : 2D\in\mathfrak p_v\}$ with the levels `levels`. -/
@[kb "weil1982" "Thm 2.3.1 (local ratios, finite places) [unverified]"]
theorem exists_finiteFactor_sqrt (hD : D ≠ 0) :
    ∃ (Af : Set (FiniteAdeleRing (𝓞 E) E)ˣ) (N : ℝ≥0∞) (K' : Set (SOAf (diagForm1 D))),
      MeasurableSet Af ∧ MeasurableSet K' ∧
      (∀ x, fibFinSO E (hdD S) hD Af x = N * K'.indicator 1 x) ∧
      muFinUnits E Af = ENNReal.ofReal (finRatio D) *
        (N * Measure.muFin (diagForm1 D) (lamL (chiE F E)) K') ∧
      N * Measure.muFin (diagForm1 D) (lamL (chiE F E)) K' ≠ 0 ∧
      N * Measure.muFin (diagForm1 D) (lamL (chiE F E)) K' ≠ ⊤ := by
  classical
  have hfin := finite_bad_places hD
  set Sfin : Finset (HeightOneSpectrum (𝓞 F)) := hfin.toFinset with hSfin
  have hS : ∀ v ∉ Sfin, (2 * D : 𝓞 F) ∉ v.asIdeal := fun v hv h => hv (hfin.mem_toFinset.2 h)
  set k : HeightOneSpectrum (𝓞 F) → ℕ := levels S hD with hk
  have hk1 : ∀ v ∈ Sfin, 1 ≤ k v := fun v _ =>
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hkc : ∀ v ∈ Sfin, cv S v ≤ k v := fun v _ =>
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hk3 : ∀ v ∈ Sfin, 3 * sExp v + 2 * eExp D hD v + 1 ≤ k v := fun v _ => le_max_right _ _
  have hF := prod_boxF_pos Sfin k
  have hK := prod_Kp_pos S Sfin k hD
  have hprod : muFinUnits F (boxF Sfin k) * Measure.muFin (diagForm1 D) (lamL (chiE F E)) (Kp S Sfin k) =
      ENNReal.ofReal ((ohatVol F * ∏ v ∈ Sfin, (qn v)⁻¹ ^ k v * (1 - (qn v)⁻¹)⁻¹) *
        ∏ v ∈ Sfin, Aloc S k hD v * (1 - chiE F E v / qn v)⁻¹) := by
    rw [muFinUnits_boxF Sfin k hk1, muFin_Kp S Sfin k hD hk1 hkc hk3 hS, ← ENNReal.ofReal_mul hF.le]
  refine ⟨boxE E Sfin k, muFinUnits F (boxF Sfin k), Kp S Sfin k, ?_, ?_, fun x => fibFinSO_eq S Sfin k hD hk1 hS x,
    finite_ratio S Sfin k hD hk1 hkc hk3 hS, ?_, ?_⟩
  · exact measurableSet_ideleBox _ _ (fun w _ => by rw [winE_eq]; exact measurableSet_oneAdd w _)
  · exact measurableSet_boxSO (diagForm1 D) Sfin (Uloc S k) (fun v hv => measurableSet_Uloc S k v hD (hk1 v hv))
  · rw [hprod]; exact (ENNReal.ofReal_pos.2 (mul_pos hF hK)).ne'
  · rw [hprod]; exact ENNReal.ofReal_ne_top

end Package

/-! ### The finite factor for an arbitrary basis $(1,\delta)$ of $E/F$ -/

section Basis

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E] {D : 𝓞 F}

/-- **The finite factor of the measure comparison, for an arbitrary $F$-basis $(1,\delta)$ of $E$ with $\delta^2 = d = -D$**
(the form in which `torComparison_of_finiteFactor` consumes it). Reduces to `exists_finiteFactor_sqrt`: the basis is
`sqrtBasis` of the `SqrtData` $\theta = \delta$ (the conjugation sends $\delta$ to $-\delta$ since it fixes no element of
$E\setminus F$). -/
@[kb "weil1982" "Thm 2.3.1 (local ratios, finite places) [unverified]"]
theorem exists_finiteFactor {b : Module.Basis (Fin 2) F E} (hb0 : b 0 = 1)
    (hb1 : b 1 * b 1 = algebraMap F E (dD D)) (hD : D ≠ 0) :
    ∃ (Af : Set (FiniteAdeleRing (𝓞 E) E)ˣ) (N : ℝ≥0∞) (K' : Set (SOAf (diagForm1 D))),
      MeasurableSet Af ∧ MeasurableSet K' ∧
      (∀ x, fibFinSO E hb1 hD Af x = N * K'.indicator 1 x) ∧
      muFinUnits E Af = ENNReal.ofReal (finRatio D) *
        (N * Measure.muFin (diagForm1 D) (lamL (chiE F E)) K') ∧
      N * Measure.muFin (diagForm1 D) (lamL (chiE F E)) K' ≠ 0 ∧
      N * Measure.muFin (diagForm1 D) (lamL (chiE F E)) K' ≠ ⊤ := by
  have : Algebra.IsQuadraticExtension F E := ⟨by rw [Module.finrank_eq_card_basis b]; simp⟩
  have hsq : (b 1) ^ 2 = -algebraMap F E (algebraMap (𝓞 F) F D) := by
    rw [sq, hb1, dD, map_neg]
  have hspan : ∀ y : E, y = algebraMap F E (b.repr y 0) + algebraMap F E (b.repr y 1) * b 1 := by
    intro y
    conv_lhs => rw [← b.sum_repr y]
    rw [Fin.sum_univ_two, hb0, Algebra.smul_def, Algebra.smul_def, mul_one]
  have hconj : Binary.Rel.conj F E (b 1) = -(b 1) := by
    have hprod : (Binary.Rel.conj F E (b 1) - b 1) * (Binary.Rel.conj F E (b 1) + b 1) = 0 := by
      have : (Binary.Rel.conj F E (b 1)) ^ 2 = (b 1) ^ 2 := by
        rw [← map_pow, hsq, map_neg, AlgEquiv.commutes]
      linear_combination this
    rcases mul_eq_zero.mp hprod with h | h
    · exfalso
      apply Binary.Rel.conj_ne_one F E
      ext y
      rw [sub_eq_zero] at h
      rw [hspan y]
      simp [h]
    · linear_combination h
  let S : SqrtData D E := ⟨b 1, hsq, hconj, hD⟩
  have hbS : sqrtBasis S = b := by
    refine Module.Basis.eq_of_apply_eq fun i => ?_
    fin_cases i
    · exact (sqrtBasis_zero S).trans hb0.symm
    · exact sqrtBasis_one S
  have main := exists_finiteFactor_sqrt S hD
  have key : ∀ (c : Module.Basis (Fin 2) F E) (_ : sqrtBasis S = c) (hc1 : c 1 * c 1 = algebraMap F E (dD D)),
      ∃ (Af : Set (FiniteAdeleRing (𝓞 E) E)ˣ) (N : ℝ≥0∞) (K' : Set (SOAf (diagForm1 D))),
        MeasurableSet Af ∧ MeasurableSet K' ∧
        (∀ x, fibFinSO E hc1 hD Af x = N * K'.indicator 1 x) ∧
        muFinUnits E Af = ENNReal.ofReal (finRatio D) *
          (N * Measure.muFin (diagForm1 D) (lamL (chiE F E)) K') ∧
        N * Measure.muFin (diagForm1 D) (lamL (chiE F E)) K' ≠ 0 ∧
        N * Measure.muFin (diagForm1 D) (lamL (chiE F E)) K' ≠ ⊤ := by
    intro c hc hc1
    subst hc
    exact main
  exact key b hbS hb1

end Basis

end QuadFormsKB.Tamagawa.Measure.Weil
