import QuadFormsKB.Tamagawa.Measure.Weil.QuatResidue
import QuadFormsKB.Tamagawa.Measure.Weil.QuatLocalVolume
import QuadFormsKB.Tamagawa.Measure.Weil.GnatEichler

/-!
# The image of the adelic reduced norm

$\mathbb H = \mathbb H[F,a,b]$ over any number field $F$, $a, b\in F^\times$ (no integrality, no division hypothesis).
We determine the image of $\operatorname{nrd} : (\mathbb H\otimes\mathbb A)^\times\to\mathbb A^\times$:

* **`exists_sq_sub_mul_sq_eq`** (local, integral): at a finite place $v\nmid 2$ with $\alpha\in\mathcal O_v^\times$,
  every $u\in\mathcal O_v^\times$ is $x^2-\alpha y^2$ with $x, y\in\mathcal O_v$ (a solution mod $v$ from
  Mathlib's `FiniteField.exists_root_sum_quadratic`, lifted by the library's local square theorem
  `HN.isSquare_of_valued_sub_one_lt`).
* `exists_real_nrd`, `exists_complex_sq`: the archimedean local images ($\mathbb R^\times$ at split real places,
  $\mathbb R_{>0}$ at ramified real places, $\mathbb C^\times$ at complex places).
* **`exists_nrdUnit_eq`**: an idele $u$ is a reduced norm of $(\mathbb H\otimes\mathbb A)^\times$ as soon as
  $u_w > 0$ at the real places $w$ where $\mathbb H$ ramifies ($\sigma_w(a),\sigma_w(b) < 0$, `IsRamifiedReal`). At the
  finite places the local solutions are `exists_nrd_eq_finite'` (every quaternary form over a $p$-adic field is
  universal), chosen integral at the almost all places where $v\nmid 2ab$ and $u_v\in\mathcal O_v^\times$.
* **`nrdUnit_pos_of_ramified`**: conversely $\operatorname{nrd}(x)_w > 0$ at ramified real $w$.

Together: $\operatorname{nrd}((\mathbb H\otimes\mathbb A)^\times) = \mathbb A^\times_+ :=
\{u : u_w > 0 \text{ for ramified real } w\}$ (Weil 1982, §3.? [unverified]; Voight 2021, §13.4, §14.7 [unverified]).
-/

open IsDedekindDomain NumberField NumberField.InfinitePlace MeasureTheory Filter Topology Set Polynomial
open scoped ENNReal NNReal Quaternion

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

/-- $\operatorname{re}(x\bar x) = x_0^2 - c_1x_1^2 - c_3x_2^2 + c_1c_3x_3^2$ in $\mathbb H[R, c_1, 0, c_3]$. -/
theorem re_mul_star_eq {R : Type*} [CommRing R] (c₁ c₃ : R) (x : ℍ[R, c₁, 0, c₃]) :
    (x * star x).re = x.re ^ 2 - c₁ * x.imI ^ 2 - c₃ * x.imJ ^ 2 + c₁ * c₃ * x.imK ^ 2 := by
  simp [QuaternionAlgebra.re_mul]; ring

/-- If $x\bar x$ is a unit scalar then $x$ is a unit ($x^{-1} = \bar x\,(x\bar x)^{-1}$). -/
def unitOfNrd {R : Type*} [CommRing R] {c₁ c₃ : R} (x : ℍ[R, c₁, 0, c₃]) (u : Rˣ) (h : (x * star x).re = u) :
    (ℍ[R, c₁, 0, c₃])ˣ where
  val := x
  inv := star x * ((u⁻¹ : Rˣ) : R)
  val_inv := by
    rw [← mul_assoc, QuaternionAlgebra.mul_star_eq_coe, h, ← QuaternionAlgebra.coe_mul, Units.mul_inv,
      QuaternionAlgebra.coe_one]
  inv_val := by
    have hc : star x * (((u⁻¹ : Rˣ) : R) : ℍ[R, c₁, 0, c₃]) = ((u⁻¹ : Rˣ) : R) * star x :=
      (QuaternionAlgebra.coe_commutes _ _).symm
    have hre : (star x * x).re = (x * star x).re := by simp [QuaternionAlgebra.re_mul]
    rw [hc, mul_assoc, QuaternionAlgebra.star_mul_eq_coe, hre, h, ← QuaternionAlgebra.coe_mul, Units.inv_mul,
      QuaternionAlgebra.coe_one]

theorem coe_unitOfNrd {R : Type*} [CommRing R] {c₁ c₃ : R} (x : ℍ[R, c₁, 0, c₃]) (u : Rˣ)
    (h : (x * star x).re = u) : (unitOfNrd x u h : ℍ[R, c₁, 0, c₃]) = x := rfl

/-! ### The local integral statement at the good places -/

section Local

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Kv" => v.adicCompletion F
local notation "Ov" => v.adicCompletionIntegers F
local notation "kv" => IsLocalRing.ResidueField (v.adicCompletionIntegers F)

theorem valued_le_one_of_sq_le_one {x : Kv} (h : Valued.v x ^ 2 ≤ 1) : Valued.v x ≤ 1 := by
  by_contra hx
  push Not at hx
  exact absurd h (not_le.2 (one_lt_pow₀ hx two_ne_zero))

/-- **Lifting a square root from the residue field**: if $c, s\in\mathcal O_v$, $\bar s\ne0$, $\bar c = \bar s^2$ and
$v\nmid2$, then $c = x^2$ with $x\in\mathcal O_v$. -/
theorem exists_sq_eq_of_residue (hv2 : Valued.v (2 : Kv) = 1) (c s : Ov) (hs : IsLocalRing.residue Ov s ≠ 0)
    (hc : IsLocalRing.residue Ov c = IsLocalRing.residue Ov s ^ 2) :
    ∃ x : Kv, Valued.v x ≤ 1 ∧ x ^ 2 = c := by
  have hsv : Valued.v (s : Kv) = 1 := (valued_eq_one_iff_residue_ne_zero v s).2 hs
  have hs0 : (s : Kv) ≠ 0 := by intro h; rw [h, map_zero] at hsv; exact zero_ne_one hsv
  have hres : IsLocalRing.residue Ov (c - s ^ 2) = 0 := by rw [map_sub, map_pow, hc, sub_self]
  have hlt : Valued.v ((c : Kv) - (s : Kv) ^ 2) < 1 := by
    have := (residue_eq_zero_iff v (c - s ^ 2)).1 hres
    simpa using this
  have h4 : Valued.v (4 : Kv) = 1 := by
    rw [show (4 : Kv) = 2 * 2 by norm_num, map_mul, hv2, one_mul]
  have hsq : IsSquare ((c : Kv) / (s : Kv) ^ 2) := by
    refine HN.isSquare_of_valued_sub_one_lt v _ ?_
    rw [h4, show (c : Kv) / (s : Kv) ^ 2 - 1 = ((c : Kv) - (s : Kv) ^ 2) / (s : Kv) ^ 2 by
      field_simp, map_div₀, map_pow, hsv, one_pow, div_one]
    exact hlt
  obtain ⟨r, hr⟩ := hsq
  refine ⟨r * s, ?_, ?_⟩
  · refine valued_le_one_of_sq_le_one v ?_
    have hx2 : (r * (s : Kv)) ^ 2 = c := by
      rw [mul_pow, sq r, ← hr]; field_simp
    rw [← map_pow, hx2]; exact c.2
  · rw [mul_pow, sq r, ← hr]; field_simp

/-- **Binary unit forms are universal on units at $v\nmid2$**: if $\alpha, u\in\mathcal O_v^\times$ then
$u = x^2-\alpha y^2$ with $x, y\in\mathcal O_v$. -/
@[kb "omeara1963" "§92:1 (unimodular forms over a non-dyadic local ring represent all units) [unverified]"]
theorem exists_sq_sub_mul_sq_eq (hv2 : Valued.v (2 : Kv) = 1) {α u : Kv} (hα : Valued.v α = 1)
    (hu : Valued.v u = 1) :
    ∃ x y : Kv, Valued.v x ≤ 1 ∧ Valued.v y ≤ 1 ∧ x ^ 2 - α * y ^ 2 = u := by
  classical
  let _ : Fintype kv := Fintype.ofFinite kv
  have hαO : α ∈ Ov := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hα.le
  have huO : u ∈ Ov := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hu.le
  set α' : Ov := ⟨α, hαO⟩
  set u' : Ov := ⟨u, huO⟩
  have hα0 : IsLocalRing.residue Ov α' ≠ 0 := (valued_eq_one_iff_residue_ne_zero v α').1 hα
  have hu0 : IsLocalRing.residue Ov u' ≠ 0 := (valued_eq_one_iff_residue_ne_zero v u').1 hu
  have hodd : Fintype.card kv % 2 = 1 := FiniteField.odd_card_of_char_ne_two (ringChar_ne_two_of_valued_two v hv2)
  have hf : (X ^ 2 : kv[X]).degree = 2 := by rw [degree_X_pow]; rfl
  have hg : (-(C (IsLocalRing.residue Ov α')) * X ^ 2 - C (IsLocalRing.residue Ov u') : kv[X]).degree = 2 := by
    compute_degree!
    simpa using hα0
  obtain ⟨s, t, hst⟩ := FiniteField.exists_root_sum_quadratic hf hg hodd
  simp only [eval_pow, eval_X, eval_sub, eval_mul, eval_neg, eval_C] at hst
  -- hst : s ^ 2 + (-ā * t ^ 2 - ū) = 0
  by_cases hs : s ≠ 0
  · -- y := lift t, x² = u + α y²
    set y₀ := liftV v t
    obtain ⟨x, hx, hx2⟩ := exists_sq_eq_of_residue v hv2 (u' + α' * y₀ ^ 2) (liftV v s)
      (by rw [residue_liftV]; exact hs)
      (by rw [map_add, map_mul, map_pow, residue_liftV, residue_liftV]; linear_combination -hst)
    refine ⟨x, y₀, hx, y₀.2, ?_⟩
    rw [hx2]; push_cast; ring
  · -- s = 0: x := 0, y² = −u/α
    push Not at hs
    subst hs
    have hβO : α⁻¹ ∈ Ov := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hα, inv_one]
    set β' : Ov := ⟨α⁻¹, hβO⟩
    have hαβ : α' * β' = 1 := by
      apply Subtype.ext
      have hα0' : α ≠ 0 := by intro h; rw [h, map_zero] at hα; exact zero_ne_one hα
      change α * α⁻¹ = 1
      exact mul_inv_cancel₀ hα0'
    have hβres : IsLocalRing.residue Ov β' * IsLocalRing.residue Ov α' = 1 := by
      rw [mul_comm, ← map_mul, hαβ, map_one]
    have ht : t ≠ 0 := by
      rintro rfl
      apply hu0
      linear_combination -hst
    obtain ⟨y, hy, hy2⟩ := exists_sq_eq_of_residue v hv2 (-u' * β') (liftV v t)
      (by rw [residue_liftV]; exact ht)
      (by
        rw [map_mul, map_neg, residue_liftV]
        linear_combination (IsLocalRing.residue Ov β') * hst + t ^ 2 * hβres)
    refine ⟨0, y, by simp, hy, ?_⟩
    rw [hy2]
    have hα0' : α ≠ 0 := by intro h; rw [h, map_zero] at hα; exact zero_ne_one hα
    change (0 : Kv) ^ 2 - α * (-u * α⁻¹) = u
    field_simp
    ring

end Local

/-! ### Archimedean local images -/

/-- At a real place: $u\ne0$ is $x_0^2-\alpha x_1^2-\beta x_2^2+\alpha\beta x_3^2$ unless $\alpha,\beta<0<-u$. -/
theorem exists_real_nrd {α β u : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0) (hu : u ≠ 0) (h : ¬(α < 0 ∧ β < 0) ∨ 0 < u) :
    ∃ x : Fin 4 → ℝ, x 0 ^ 2 - α * x 1 ^ 2 - β * x 2 ^ 2 + α * β * x 3 ^ 2 = u := by
  rcases lt_or_gt_of_ne hu with hneg | hpos
  · have hab : 0 < α ∨ 0 < β := by
      rcases h with h | h
      · by_contra hc; push Not at hc
        exact h ⟨lt_of_le_of_ne hc.1 hα, lt_of_le_of_ne hc.2 hβ⟩
      · exact absurd h (not_lt.2 hneg.le)
    rcases hab with ha | hb
    · refine ⟨![0, Real.sqrt (-u / α), 0, 0], ?_⟩
      simp only [Matrix.cons_val]
      rw [Real.sq_sqrt (div_nonneg (neg_nonneg.2 hneg.le) ha.le)]
      field_simp; ring
    · refine ⟨![0, 0, Real.sqrt (-u / β), 0], ?_⟩
      simp only [Matrix.cons_val]
      rw [Real.sq_sqrt (div_nonneg (neg_nonneg.2 hneg.le) hb.le)]
      field_simp; ring
  · refine ⟨![Real.sqrt u, 0, 0, 0], ?_⟩
    simp only [Matrix.cons_val]
    rw [Real.sq_sqrt hpos.le]; ring

/-! ### The adelic statement -/

section Adelic

variable {F : Type} [Field F] [NumberField F] {a b : F}

local notation "AF" => FiniteAdeleRing (𝓞 F) F

theorem diag_fst_fst (c : F) (w : {w : InfinitePlace F // w.IsReal}) :
    (diag F c).1.1 w = embedding_of_isReal w.2 c :=
  mixedEmbedding.mixedEmbedding_apply_isReal F c w

theorem diag_snd_apply (c : F) (v : HeightOneSpectrum (𝓞 F)) :
    (diag F c).2 v = algebraMap F (v.adicCompletion F) c := rfl

/-- The finite components of an idele are eventually units of $\mathcal O_v$. -/
theorem eventually_valued_idele_eq_one (u : (Adeles F)ˣ) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, Valued.v ((u : Adeles F).2 v) = 1 := by
  have h1 : ∀ᶠ v in cofinite, (u : Adeles F).2 v ∈ v.adicCompletionIntegers F := (u : Adeles F).2.2
  have h2 : ∀ᶠ v in cofinite, ((u⁻¹ : (Adeles F)ˣ) : Adeles F).2 v ∈ v.adicCompletionIntegers F :=
    ((u⁻¹ : (Adeles F)ˣ) : Adeles F).2.2
  filter_upwards [h1, h2] with v hv1 hv2
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hv1 hv2
  have hmul : (u : Adeles F).2 v * ((u⁻¹ : (Adeles F)ˣ) : Adeles F).2 v = 1 :=
    congrArg (fun z : Adeles F => z.2 v) u.mul_inv
  have hval := congrArg Valued.v hmul
  rw [map_mul, map_one] at hval
  refine le_antisymm hv1 ?_
  by_contra hlt; push Not at hlt
  have hlt' : Valued.v ((u : Adeles F).2 v) * Valued.v (((u⁻¹ : (Adeles F)ˣ) : Adeles F).2 v) < 1 :=
    mul_lt_one_of_lt_of_le hlt hv2
  rw [hval] at hlt'; exact lt_irrefl _ hlt'

theorem idele_snd_ne_zero (u : (Adeles F)ˣ) (v : HeightOneSpectrum (𝓞 F)) : (u : Adeles F).2 v ≠ 0 := by
  intro h
  have := congrArg (fun z : Adeles F => z.2 v) u.mul_inv
  change (u : Adeles F).2 v * ((u⁻¹ : (Adeles F)ˣ) : Adeles F).2 v = 1 at this
  rw [h, zero_mul] at this; exact zero_ne_one this

theorem idele_fst_fst_ne_zero (u : (Adeles F)ˣ) (w : {w : InfinitePlace F // w.IsReal}) :
    (u : Adeles F).1.1 w ≠ 0 := by
  intro h
  have := congrArg (fun z : Adeles F => z.1.1 w) u.mul_inv
  change (u : Adeles F).1.1 w * ((u⁻¹ : (Adeles F)ˣ) : Adeles F).1.1 w = 1 at this
  rw [h, zero_mul] at this; exact zero_ne_one this

/-- A good finite place for $u$: $v\nmid2$, $a, b, u_v\in\mathcal O_v^\times$. -/
def GoodFor (a b : F) (u : (Adeles F)ˣ) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  Valued.v (2 : v.adicCompletion F) = 1 ∧ Valued.v (algebraMap F (v.adicCompletion F) a) = 1 ∧
    Valued.v (algebraMap F (v.adicCompletion F) b) = 1 ∧ Valued.v ((u : Adeles F).2 v) = 1

theorem eventually_goodFor (ha0 : a ≠ 0) (hb0 : b ≠ 0) (u : (Adeles F)ˣ) :
    ∀ᶠ v in cofinite, GoodFor a b u v := by
  filter_upwards [eventually_good_place ha0 hb0, eventually_valued_idele_eq_one u] with v h1 h2
  exact ⟨h1.1, h1.2.1, h1.2.2.1, h2⟩

/-- **The local solution** $y_v\in\mathbb H[F_v,a,b]$ with $\operatorname{nrd}(y_v) = u_v$, integral at good places. -/
theorem exists_local_nrd (ha0 : a ≠ 0) (hb0 : b ≠ 0) (u : (Adeles F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ y : QuatV a b v, (y * star y).re = (u : Adeles F).2 v ∧
      (GoodFor a b u v → ∀ i, (QuaternionAlgebra.linearEquivTuple _ _ _ y) i ∈ v.adicCompletionIntegers F) := by
  classical
  by_cases hg : GoodFor a b u v
  · obtain ⟨x, y, hx, hy, hxy⟩ := exists_sq_sub_mul_sq_eq v hg.1 hg.2.1 hg.2.2.2
    refine ⟨⟨x, y, 0, 0⟩, ?_, fun _ i => ?_⟩
    · rw [re_mul_star_eq]; simp only; rw [← hxy]; ring
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      fin_cases i
      · exact hx
      · exact hy
      · simp
      · simp
  · obtain ⟨y, hy⟩ := QuadFormsKB.Quat.exists_nrd_eq_finite' ha0 hb0 v (idele_snd_ne_zero u v)
    refine ⟨⟨y.re, y.imI, y.imJ, y.imK⟩, ?_, fun h => absurd h hg⟩
    rw [re_mul_star_eq]; rw [← hy]; rfl

/-- The local solutions at the finite places. -/
def locSol (ha0 : a ≠ 0) (hb0 : b ≠ 0) (u : (Adeles F)ˣ) (v : HeightOneSpectrum (𝓞 F)) : QuatV a b v :=
  (exists_local_nrd ha0 hb0 u v).choose

theorem locSol_spec (ha0 : a ≠ 0) (hb0 : b ≠ 0) (u : (Adeles F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (locSol ha0 hb0 u v * star (locSol ha0 hb0 u v)).re = (u : Adeles F).2 v :=
  (exists_local_nrd ha0 hb0 u v).choose_spec.1

theorem locSol_integral (ha0 : a ≠ 0) (hb0 : b ≠ 0) (u : (Adeles F)ˣ) (i : Fin 4) :
    ∀ᶠ v in cofinite, (QuaternionAlgebra.linearEquivTuple _ _ _ (locSol ha0 hb0 u v)) i ∈
      v.adicCompletionIntegers F := by
  filter_upwards [eventually_goodFor ha0 hb0 u] with v hv
  exact (exists_local_nrd ha0 hb0 u v).choose_spec.2 hv i

/-- The finite coordinate adele $(y_v)_i$. -/
def finCoord (ha0 : a ≠ 0) (hb0 : b ≠ 0) (u : (Adeles F)ˣ) (i : Fin 4) : AF :=
  ⟨fun v => (QuaternionAlgebra.linearEquivTuple _ _ _ (locSol ha0 hb0 u v)) i, locSol_integral ha0 hb0 u i⟩


variable (a b) in
/-- The real places where $\mathbb H$ ramifies impose positivity: the archimedean hypothesis of
`exists_nrdUnit_eq`. -/
def PosAtRamified (u : (Adeles F)ˣ) : Prop :=
  ∀ (w : InfinitePlace F) (hw : w.IsReal), QuadFormsKB.Quat.IsRamifiedReal a b w hw → 0 < (u : Adeles F).1.1 ⟨w, hw⟩

theorem exists_realSol (ha0 : a ≠ 0) (hb0 : b ≠ 0) {u : (Adeles F)ˣ} (hpos : PosAtRamified a b u)
    (w : {w : InfinitePlace F // w.IsReal}) :
    ∃ x : Fin 4 → ℝ, x 0 ^ 2 - (diag F a).1.1 w * x 1 ^ 2 - (diag F b).1.1 w * x 2 ^ 2 +
      (diag F a).1.1 w * (diag F b).1.1 w * x 3 ^ 2 = (u : Adeles F).1.1 w := by
  rw [diag_fst_fst, diag_fst_fst]
  refine exists_real_nrd ((_root_.map_ne_zero _).2 ha0) ((_root_.map_ne_zero _).2 hb0) (idele_fst_fst_ne_zero u w) ?_
  by_cases h : embedding_of_isReal w.2 a < 0 ∧ embedding_of_isReal w.2 b < 0
  · exact Or.inr (hpos w.1 w.2 h)
  · exact Or.inl h

/-- The finite coordinates `finCoord` together with archimedean local solutions. -/
def nrdPreimage (ha0 : a ≠ 0) (hb0 : b ≠ 0) (u : (Adeles F)ˣ) (hpos : PosAtRamified a b u) : QuatAdele a b :=
  let R : {w : InfinitePlace F // w.IsReal} → Fin 4 → ℝ := fun w => (exists_realSol ha0 hb0 hpos w).choose
  let Z : {w : InfinitePlace F // w.IsComplex} → ℂ := fun w =>
    (IsAlgClosed.exists_pow_nat_eq ((u : Adeles F).1.2 w) two_pos).choose
  let c : Fin 4 → Adeles F := fun i => ((fun w => R w i, fun w => if i = 0 then Z w else 0), finCoord ha0 hb0 u i)
  ⟨c 0, c 1, c 2, c 3⟩

theorem nrdPreimage_re_mul_star (ha0 : a ≠ 0) (hb0 : b ≠ 0) (u : (Adeles F)ˣ) (hpos : PosAtRamified a b u) :
    (nrdPreimage ha0 hb0 u hpos * star (nrdPreimage ha0 hb0 u hpos)).re = (u : Adeles F) := by
  rw [re_mul_star_eq]
  refine Prod.ext (Prod.ext (funext fun w => ?_) (funext fun w => ?_)) ?_
  · have := (exists_realSol ha0 hb0 hpos w).choose_spec
    simpa [nrdPreimage] using this
  · have := (IsAlgClosed.exists_pow_nat_eq ((u : Adeles F).1.2 w) two_pos).choose_spec
    simpa [nrdPreimage] using this
  · apply RestrictedProduct.ext; intro v
    have := locSol_spec ha0 hb0 u v
    rw [re_mul_star_eq] at this
    simp only [Prod.snd_add, Prod.snd_sub, Prod.snd_mul, Prod.pow_snd]
    exact this

/-- **The image of the adelic reduced norm**: every idele that is positive at the real places where $\mathbb H$
ramifies is $\operatorname{nrd}(x)$ for some $x\in(\mathbb H\otimes\mathbb A)^\times$. -/
@[kb "voight2021" "§13.4 (local norms), Thm 14.7.4 (positivity at ramified real places) [unverified]"]
theorem exists_nrdUnit_eq (ha0 : a ≠ 0) (hb0 : b ≠ 0) (u : (Adeles F)ˣ) (hpos : PosAtRamified a b u) :
    ∃ x : (QuatAdele a b)ˣ, nrdUnit x = u :=
  ⟨unitOfNrd _ u (nrdPreimage_re_mul_star ha0 hb0 u hpos), Units.ext (by
    rw [nrdUnit_val, coe_unitOfNrd, nrdPreimage_re_mul_star])⟩

/-- **Reduced norms are positive at ramified real places.** -/
theorem nrdUnit_pos_of_ramified (x : (QuatAdele a b)ˣ) : PosAtRamified a b (nrdUnit x) := by
  intro w hw hram
  obtain ⟨hσa, hσb⟩ := hram
  have hval : ((nrdUnit x : Adeles F)).1.1 ⟨w, hw⟩ = ((x : QuatAdele a b).re.1.1 ⟨w, hw⟩) ^ 2 +
      (-embedding_of_isReal hw a) * ((x : QuatAdele a b).imI.1.1 ⟨w, hw⟩) ^ 2 +
      (-embedding_of_isReal hw b) * ((x : QuatAdele a b).imJ.1.1 ⟨w, hw⟩) ^ 2 +
      (embedding_of_isReal hw a * embedding_of_isReal hw b) * ((x : QuatAdele a b).imK.1.1 ⟨w, hw⟩) ^ 2 := by
    rw [nrdUnit_val, re_mul_star_eq]
    have ha' := diag_fst_fst a ⟨w, hw⟩
    have hb' := diag_fst_fst b ⟨w, hw⟩
    simp only [Prod.fst_add, Prod.fst_sub, Prod.fst_mul, Prod.pow_fst, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
      Pi.pow_apply, ha', hb']
    ring
  have hne : ((nrdUnit x : Adeles F)).1.1 ⟨w, hw⟩ ≠ 0 := idele_fst_fst_ne_zero _ _
  rw [hval] at hne ⊢
  have h1 : 0 < -embedding_of_isReal hw a := neg_pos.2 hσa
  have h2 : 0 < -embedding_of_isReal hw b := neg_pos.2 hσb
  have h3 : 0 < embedding_of_isReal hw a * embedding_of_isReal hw b := mul_pos_of_neg_of_neg hσa hσb
  refine lt_of_le_of_ne (by positivity) (Ne.symm hne)

end Adelic

end

end QuadFormsKB.Tamagawa.Measure.Weil
