import QuadFormsKB.Tamagawa.Measure.Weil.SplitSL1Local

/-!
# The finite part of the box, for split $D$

**Layer:** $F$ a number field, $a, b\in F^\times$ integral at every finite place, $x, y\in F$ with $x^2 - ay^2 = b$.

* `phiFin` $=\Phi_f : \mathbb H[\mathbb A_f,a,b]\to M_2(\mathbb A_f)$; its component at $v$ is $\Phi_v$ (`phiFin_apply_v`).
* `finQuatBox` $=\{u : \Phi_f(u), \Phi_f(u^{-1})\in M_2(\hat{\mathcal O})\} = \prod_v U_v$ (`mem_finQuatBox_iff`), and $U_v = \Lambda_v^\times$
  outside the finite set of places where $2ab$ is not a unit or $x, y$ are not integral (`badPlaces`), so `finQuatBox` is a
  chart box (`finQuatBox_eq_quatBox`).
* **`muFinQuat_finQuatBox`**: $\mu_f(\mathrm{finQuatBox}) = \prod_v\lambda_v^{-1}\omega_v(U_v)$.
-/

open MeasureTheory Measure Set NumberField IsDedekindDomain Filter
open scoped ENNReal NNReal Classical

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F

variable {a b x y : F} (h : x ^ 2 - a * y ^ 2 = b)

include h in
theorem split_fin : (algebraMap F AF x) ^ 2 - (algebraMap F AF a) * (algebraMap F AF y) ^ 2 = algebraMap F AF b := by
  simp only [← map_pow, ← map_mul, ← map_sub, h]

/-- $\Phi_f : \mathbb H[\mathbb A_f,a,b]\to M_2(\mathbb A_f)$. -/
def phiFin : QuatFin a b →ₐ[AF] Matrix (Fin 2) (Fin 2) AF :=
  quatMatHom (algebraMap F AF a) (algebraMap F AF b) (algebraMap F AF x) (algebraMap F AF y) (split_fin h)

/-- The component of $\Phi_f$ at $v$ is $\Phi_v$. -/
theorem phiFin_apply_v (q : QuatFin a b) (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2) :
    (phiFin h q i j) v = phiV v h (projQ a b v q) i j := by
  rw [phiFin, phiV, quatMatHom_apply, quatMatHom_apply]
  fin_cases i <;> fin_cases j <;> rfl

/-- The finite part of the box: $\Phi_f(u), \Phi_f(u^{-1})\in M_2(\hat{\mathcal O})$. -/
def finQuatBox : Set (QuatFin a b)ˣ :=
  {u | (∀ i j, phiFin h (u : QuatFin a b) i j ∈ OHat) ∧
    (∀ i j, phiFin h ((u⁻¹ : (QuatFin a b)ˣ) : QuatFin a b) i j ∈ OHat)}

theorem mem_finQuatBox_iff (u : (QuatFin a b)ˣ) : u ∈ finQuatBox h ↔ ∀ v, unitAtQ a b v u ∈ UV v h := by
  have hinv : ∀ v, (((unitAtQ a b v u)⁻¹ : (QuatV a b v)ˣ) : QuatV a b v) =
      projQ a b v ((u⁻¹ : (QuatFin a b)ˣ) : QuatFin a b) := fun v => by
    rw [← map_inv]; rfl
  simp only [finQuatBox, UV, Set.mem_ofPred_eq, IntMV, OHat, hinv, unitAtQ_val, ← phiFin_apply_v h]
  constructor
  · rintro ⟨h1, h2⟩ v
    exact ⟨fun i j => h1 i j v, fun i j => h2 i j v⟩
  · intro h1
    exact ⟨fun i j v => (h1 v).1 i j, fun i j v => (h1 v).2 i j⟩

/-- The good places: $2, a, b$ units and $x, y$ integral. -/
def IsGoodPlace (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  Valued.v (2 : v.adicCompletion F) = 1 ∧ Valued.v (algebraMap F (v.adicCompletion F) a) = 1 ∧
    Valued.v (algebraMap F (v.adicCompletion F) b) = 1 ∧ algebraMap F (v.adicCompletion F) x ∈
      v.adicCompletionIntegers F ∧ algebraMap F (v.adicCompletion F) y ∈ v.adicCompletionIntegers F

theorem eventually_integral (c : F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, algebraMap F (v.adicCompletion F) c ∈ v.adicCompletionIntegers F := by
  by_cases hc : c = 0
  · exact Filter.Eventually.of_forall fun v => by rw [hc, map_zero]; exact zero_mem _
  · filter_upwards [eventually_good_place hc hc] with v hv
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hv.2.1.le

theorem eventually_isGoodPlace (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, IsGoodPlace (a := a) (b := b) (x := x) (y := y) v := by
  filter_upwards [eventually_good_place ha0 hb0, eventually_integral x, eventually_integral y] with v hv hx hy
  exact ⟨hv.1, hv.2.1, hv.2.2.1, hx, hy⟩

/-- The finite set of bad places. -/
def badPlaces (ha0 : a ≠ 0) (hb0 : b ≠ 0) : Finset (HeightOneSpectrum (𝓞 F)) :=
  (Filter.eventually_cofinite.1 (eventually_isGoodPlace (x := x) (y := y) ha0 hb0)).toFinset

theorem isGoodPlace_of_not_mem_badPlaces (ha0 : a ≠ 0) (hb0 : b ≠ 0) {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ badPlaces (x := x) (y := y) ha0 hb0) : IsGoodPlace (a := a) (b := b) (x := x) (y := y) v := by
  by_contra hn
  exact hv ((Set.Finite.mem_toFinset _).2 hn)

theorem UV_eq_of_not_mem_badPlaces (ha0 : a ≠ 0) (hb0 : b ≠ 0) {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ badPlaces (x := x) (y := y) ha0 hb0) : UV v h = lamLocUnits a b v := by
  obtain ⟨h2, hav, hbv, hx, hy⟩ := isGoodPlace_of_not_mem_badPlaces ha0 hb0 hv
  exact UV_eq_lamLocUnits v h h2 hav hbv hx hy

/-- **`finQuatBox` is a chart box.** -/
theorem finQuatBox_eq_quatBox (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    finQuatBox h = quatBox a b (badPlaces (x := x) (y := y) ha0 hb0) fun v => UV v h := by
  ext u
  rw [mem_finQuatBox_iff]
  simp only [quatBox, ChartData.chartBox, Set.mem_ofPred_eq]
  refine forall_congr' fun v => ?_
  change _ ↔ unitAtQ a b v u ∈ _
  split_ifs with hv
  · rfl
  · rw [UV_eq_of_not_mem_badPlaces h ha0 hb0 hv]; rfl

theorem measurableSet_UV (v : HeightOneSpectrum (𝓞 F)) : MeasurableSet (UV v h) := by
  have hc : Continuous fun u : (QuatV a b v)ˣ => phiV v h (u : QuatV a b v) :=
    (continuous_phiV v h).comp Units.continuous_val
  have hci : Continuous fun u : (QuatV a b v)ˣ => phiV v h ((u⁻¹ : (QuatV a b v)ˣ) : QuatV a b v) :=
    (continuous_phiV v h).comp Units.continuous_coe_inv
  have hint : ∀ {f : (QuatV a b v)ˣ → Matrix (Fin 2) (Fin 2) (v.adicCompletion F)}, Continuous f →
      MeasurableSet {u | IntMV v (f u)} := by
    intro f hf
    have : {u | IntMV v (f u)} = ⋂ i, ⋂ j, (fun u => f u i j) ⁻¹' (v.adicCompletionIntegers F : Set _) := by
      ext u; simp [IntMV, Set.mem_iInter]
    rw [this]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      ((continuous_apply j).comp ((continuous_apply i).comp hf)).measurable
        (isOpen_adicCompletionIntegers v).measurableSet
  exact (hint hc).inter (hint hci)

theorem four_ab_ne_zero (v : HeightOneSpectrum (𝓞 F)) (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    (4 * algebraMap F (v.adicCompletion F) a * algebraMap F (v.adicCompletion F) b) ≠ 0 := by
  rw [show (4 : v.adicCompletion F) = algebraMap F (v.adicCompletion F) 4 from (map_ofNat _ 4).symm, ← map_mul,
    ← map_mul]
  exact (map_ne_zero _).2 (mul_ne_zero (mul_ne_zero (by norm_num) ha0) hb0)

/-- **$\mu_f(\mathrm{finQuatBox}) = \prod_v\lambda_v^{-1}\omega_v(U_v)$.** -/
theorem muFinQuat_finQuatBox (ha : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) a) ≤ 1)
    (hb : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) b) ≤ 1)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    muFinQuat a b (finQuatBox h) =
      ENNReal.ofReal (∏' v, (ENNReal.ofReal (lamV v)⁻¹ * omegaQuatV v a b (UV v h)).toReal) := by
  have hfin : ∀ v ∈ badPlaces (x := x) (y := y) ha0 hb0, omegaQuatV v a b (UV v h) ≠ ⊤ := by
    intro v _
    rw [omegaQuatV_UV v h ha0 hb0]
    refine ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 ((hyp_adic v).md_ne_zero _ ?_)) ?_
    · exact isUnit_iff_ne_zero.2 (four_ab_ne_zero v ha0 hb0)
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top (volO_ne_top v))
  rw [finQuatBox_eq_quatBox h ha0 hb0, muFinQuat_quatBox_weil ha hb ha0 hb0 _ _ (fun v _ => measurableSet_UV h v) hfin]
  congr 1
  refine tprod_congr fun v => ?_
  split_ifs with hv
  · rfl
  · rw [UV_eq_of_not_mem_badPlaces h ha0 hb0 hv]

end QuadFormsKB.Tamagawa.Measure.Weil
