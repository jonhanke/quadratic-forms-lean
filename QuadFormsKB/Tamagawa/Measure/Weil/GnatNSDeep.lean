/-
# The bad-place ratio of the non-square model is test-set independent

**Layer:** a number field $F$, $K = F(\delta)$, $\delta^2 = d$, $\alpha = a$, $\beta = b$ in $\mathcal O_K$; a finite place $v$ of $F$ and
the places $w\mid v$ of $K$.

* **`isSq_nrdLoc_of_mem_lamCong`**: at a deep level ($2s < m$, $s + e_a\le m$) every $u\in\Lambda^{(m)}_v$ has
  $\operatorname{nrd}u\in\mathcal O_v^{\times2}$ ($u = r(1+y)$ with $y\in\Lambda'_m$ and $\operatorname{nrd}(1+y)\equiv1\bmod\mathfrak p^{2(m-s)}$,
  a square by Hensel); hence **`nL_eq_sqUnits`**: $\operatorname{nrd}\Lambda^{(m)}_v = \mathcal O_v^{\times2}$ at every deep level.
* **`exists_quatLocalUnit_eq`**: elements $(u_w)_{w\mid v}$ with $\operatorname{nrd}u_w = 1$ lift to $G^\natural(F_v)$
  (`localPi` is bijective at every place, also at the bad ones).
* **`relIndex_nsLocSub`**: for levels $M\ge m\ge$ `nsLevK`, $[Y^{(m)} : Y^{(M)}] = \prod_{w\mid v}[K^{(3)}_{m_w} : K^{(3)}_{M_w}]$, via
  the surjection $Y^{(m)}\to\prod_{w\mid v}K^{(3)}_{m_w}$, $y\mapsto(c(y_w))_w$ (`map_lamCong` and the square-root
  normalization above), and **`relIndex_nsU`**: $[U^{(m)}_v : U^{(M)}_v] = [Y^{(m)} : Y^{(M)}]$ (the kernel of $\varphi$ on $Y^{(m)}$
  is $\mathcal O_v^\times\subseteq Y^{(M)}$).
* **`muLoc_congSub_qNS_mul`**: $\mu_v(K_N)\,q^{6N} = q^{10s+3e_a+3e_b+6e_d+\min(e_a,e_b)}$ for $\langle1,-ad,-bd,abd\rangle$ and
  $N\ge2(4s+2e_a+2e_b+3e_d)+1$ (the linear count; the $SO$ side of any deep test set).
* **`NSBadDeepRatio F`** (input, named): the bad-place identity at **some** deeper level $M\ge$ `nsLevK` (free to choose),
  and **`nsBadPlaceRatio_of_deep`**: `NSBadDeepRatio F → NSBadPlaceRatio F`. This is Weil's test-set independence for the
  local Haar ratio: both sides scale by the same index when the level is raised (the $\operatorname{nrd}$ and $N_v$ factors do not
  change at deep levels).

Source: Weil 1982, §2.2-2.3 (gauge forms; the local ratio is independent of the test set), Thm 2.3.1 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSFinal

open MeasureTheory Measure Set Function Topology NumberField NumberField.InfinitePlace IsDedekindDomain Filter WithZero
open scoped ENNReal NNReal Quaternion

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Quat QuadFormsKB.Quat.Gnat LerayPadic

noncomputable section

/-! ### The reduced norm of $\Lambda^{(m)}_v$ at a deep level -/

section SqNorm

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (a b : 𝓞 F)

local notation "Fv" => v.adicCompletion F
local notation "Av" => algebraMap F (v.adicCompletion F) (a : F)
local notation "Bv" => algebraMap F (v.adicCompletion F) (b : F)

theorem valued_le_of_two_mul_le {s m : ℕ} (hs : Valued.v (2 : Fv) = exp (-(s : ℤ))) (hsm : s ≤ m) {x : Fv}
    (hx : Valued.v (2 * x) ≤ exp (-(m : ℤ))) : Valued.v x ≤ exp (-((m - s : ℕ) : ℤ)) := by
  have := valued_half_le hs hsm hx
  rwa [← mul_assoc, inv_mul_cancel₀ (two_ne_zero : (2 : Fv) ≠ 0), one_mul] at this

/-- **$\operatorname{nrd}(1+y)$ is the square of a unit** for $y\in\Lambda'_m$, $2s < m$. -/
theorem isSq_nrd_one_add_pure {s m : ℕ} (hs : Valued.v (2 : Fv) = exp (-(s : ℤ))) (h2s : 2 * s < m)
    {y : Fin 3 → Fv} (hy : y ∈ latP v m Av Bv) :
    ∃ r : Fv, Valued.v r = 1 ∧ nrd (1 + Quat.pure y : ℍ[Fv,Av,Bv]) = r ^ 2 := by
  have hA := valued_algebraMap_le_one a v
  have hB := valued_algebraMap_le_one b v
  obtain ⟨h0, h1, h2, h3⟩ := hy
  set k := m - s with hk
  have hsm : s ≤ m := by omega
  have hy0 : Valued.v (y 0) ≤ exp (-(k : ℤ)) := valued_le_of_two_mul_le v hs hsm h0
  have hy1 : Valued.v (y 1) ≤ exp (-(k : ℤ)) := valued_le_of_two_mul_le v hs hsm h1
  have hAy2 : Valued.v (Av * y 2) ≤ exp (-(k : ℤ)) :=
    valued_le_of_two_mul_le v hs hsm (by rw [← mul_assoc]; exact h2)
  have hBy2 : Valued.v (Bv * y 2) ≤ exp (-(k : ℤ)) :=
    valued_le_of_two_mul_le v hs hsm (by rw [← mul_assoc]; exact h3)
  have hee : exp (-(k : ℤ)) * exp (-(k : ℤ)) = exp (-(((2 * k - s) + s : ℕ) : ℤ)) := by
    rw [← exp_add]; congr 1; push_cast [show s ≤ 2 * k by omega]; ring
  have hsmall : Valued.v (-(Av * y 0 ^ 2) - Bv * y 1 ^ 2 + (Av * y 2) * (Bv * y 2)) ≤
      exp (-(((2 * k - s) + s : ℕ) : ℤ)) := by
    rw [← hee]
    refine (Valuation.map_add _ _ _).trans (max_le ((Valuation.map_sub _ _ _).trans (max_le ?_ ?_)) ?_)
    · rw [Valuation.map_neg, map_mul, map_pow, pow_two]
      exact (mul_le_of_le_one_left' hA).trans (mul_le_mul' hy0 hy0)
    · rw [map_mul, map_pow, pow_two]
      exact (mul_le_of_le_one_left' hB).trans (mul_le_mul' hy1 hy1)
    · rw [map_mul]; exact mul_le_mul' hAy2 hBy2
  obtain ⟨r, hr, hr1⟩ := exists_sq_eq_near_one v hs (m := 2 * k - s) (by omega)
    (t := nrd (1 + Quat.pure y : ℍ[Fv,Av,Bv])) (by
      rw [nrd_one_add_pure, show 1 - Av * y 0 ^ 2 - Bv * y 1 ^ 2 + Av * Bv * y 2 ^ 2 - 1 =
        -(Av * y 0 ^ 2) - Bv * y 1 ^ 2 + (Av * y 2) * (Bv * y 2) by ring]
      exact hsmall)
  refine ⟨r, valued_eq_one_of_sub_one_lt v (lt_of_le_of_lt hr1 ?_), hr.symm⟩
  rw [← exp_zero, exp_lt_exp]; omega

/-- **$\operatorname{nrd}\Lambda^{(m)}_v\subseteq\mathcal O_v^{\times2}$** at a deep level. -/
theorem isSq_nrdLoc_of_mem_lamCong {s eA m : ℕ} (hs : Valued.v (2 : Fv) = exp (-(s : ℤ)))
    (hA : Valued.v Av = exp (-(eA : ℤ))) (h2s : 2 * s < m) (hmA : s + eA ≤ m) (hm : 1 ≤ m)
    {u : (QuatV (a : F) (b : F) v)ˣ} (hu : u ∈ lamCong v a b m hm) :
    ∃ r : Fv, Valued.v r = 1 ∧ nrdLoc _ _ (u : QuatV (a : F) (b : F) v) = r ^ 2 := by
  obtain ⟨hre, him⟩ := (mem_lamCong_iff v a b hs hA h2s hmA hm u).1 hu
  set x := (u : QuatV (a : F) (b : F) v)
  have hr0 : x.re ≠ 0 := by intro h; rw [h, map_zero] at hre; exact zero_ne_one hre
  have hri : Valued.v (x.re⁻¹) = 1 := by rw [map_inv₀, hre, inv_one]
  obtain ⟨r, hr, hnr⟩ := isSq_nrd_one_add_pure v a b hs h2s ((smul_mem_latP_iff hri _).2 him)
  refine ⟨x.re * r, by rw [map_mul, hre, hr, one_mul], ?_⟩
  have e : nrd x = x.re ^ 2 * nrd (1 + Quat.pure (x.re⁻¹ • imv x) : ℍ[Fv,Av,Bv]) := by
    conv_lhs => rw [eq_smul_one_add_pure x hr0]
    exact nrd_smul _ _
  rw [nrdLoc_eq_nrd, e, hnr]; ring

/-- A unit scalar lies in every $\Lambda^{(m)}_v$. -/
theorem scalar_mem_lamCong {s eA m : ℕ} (hs : Valued.v (2 : Fv) = exp (-(s : ℤ)))
    (hA : Valued.v Av = exp (-(eA : ℤ))) (h2s : 2 * s < m) (hmA : s + eA ≤ m) (hm : 1 ≤ m)
    {r : Fvˣ} (hr : Valued.v (r : Fv) = 1) :
    Units.map (algebraMap Fv (QuatV (a : F) (b : F) v)).toMonoidHom r ∈ lamCong v a b m hm := by
  rw [mem_lamCong_iff v a b hs hA h2s hmA hm]
  refine ⟨by simpa using hr, ?_⟩
  have : imv ((Units.map (algebraMap Fv (QuatV (a : F) (b : F) v)).toMonoidHom r : (QuatV (a : F) (b : F) v)ˣ) :
      QuatV (a : F) (b : F) v) = 0 := by
    ext i; fin_cases i <;> simp [imv]
  rw [this]
  simp [latP]

theorem nrdLoc_algebraMap (r : Fv) :
    nrdLoc _ _ (algebraMap Fv (QuatV (a : F) (b : F) v) r) = r ^ 2 := by
  rw [nrdLoc_eq_nrd]; simp [nrd]

/-- A scalar of $\Lambda^{(m)}_v$ lies in every deeper $\Lambda^{(M)}_v$. -/
theorem mem_lamCong_of_scalar {s eA m M : ℕ} (hs : Valued.v (2 : Fv) = exp (-(s : ℤ)))
    (hA : Valued.v Av = exp (-(eA : ℤ))) (h2s : 2 * s < m) (hmA : s + eA ≤ m) (hm : 1 ≤ m) (hmM : m ≤ M)
    {u : (QuatV (a : F) (b : F) v)ˣ} (hu : u ∈ lamCong v a b m hm) {r : Fv}
    (hur : (u : QuatV (a : F) (b : F) v) = algebraMap Fv _ r) :
    u ∈ lamCong v a b M (hm.trans hmM) := by
  rw [mem_lamCong_iff v a b hs hA (by omega) (by omega) (hm.trans hmM)]
  refine ⟨((mem_lamCong_iff v a b hs hA h2s hmA hm u).1 hu).1, ?_⟩
  have : imv (u : QuatV (a : F) (b : F) v) = 0 := by
    rw [hur]; ext i; fin_cases i <;> simp [imv]
  rw [this]; simp [latP]

end SqNorm

/-! ### $\operatorname{nrd}\Lambda^{(m)}_v = \mathcal O_v^{\times2}$ at every deep level -/

section NLDeep

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F}

variable (F) in
/-- $\mathcal O_v^{\times2}\subseteq F_v^\times$. -/
def sqUnits (v : HeightOneSpectrum (𝓞 F)) : Set (v.adicCompletion F)ˣ :=
  {u | ∃ r : (v.adicCompletion F)ˣ, Valued.v (r : v.adicCompletion F) = 1 ∧ u = r ^ 2}

/-- **$\operatorname{nrd}\Lambda^{(m_v)}_v = \mathcal O_v^{\times2}$** when $2s_v < m_v$ and $s_v + e_a(v)\le m_v$. -/
theorem nL_eq_sqUnits (m : HeightOneSpectrum (𝓞 F) → ℕ) (hm1 : ∀ v, 1 ≤ m v) (ha : a ≠ 0)
    (v : HeightOneSpectrum (𝓞 F)) (h2s : 2 * sExp v < m v) (hmA : sExp v + eExp a ha v ≤ m v) :
    nL a b m hm1 v = sqUnits F v := by
  ext u
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨r, hr, hnr⟩ := isSq_nrdLoc_of_mem_lamCong v a b (valued_two_eq v) (valued_eExp a ha v) h2s hmA
      (hm1 v) hx
    have hr0 : r ≠ 0 := by intro h; rw [h, map_zero] at hr; exact zero_ne_one hr
    exact ⟨Units.mk0 r hr0, hr, Units.ext (by simp [hnr])⟩
  · rintro ⟨r, hr, rfl⟩
    refine ⟨_, scalar_mem_lamCong v a b (valued_two_eq v) (valued_eExp a ha v) h2s hmA (hm1 v) hr, Units.ext ?_⟩
    rw [nrdLocUnit_val, Units.val_pow_eq_pow_val, ← nrdLoc_algebraMap v a b]; rfl

end NLDeep

/-! ### Lifting along $D_E\otimes F_v\to\prod_{w\mid v}D'\otimes K_w$ -/

section Lift

variable {F : Type} [Field F] [NumberField F] {a b d : 𝓞 F} {K : Type} [Field K] [NumberField K] [Algebra F K]
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  {α β : 𝓞 K} (hα : (α : K) = algebraMap F K (a : F)) (hβ : (β : K) = algebraMap F K (b : F))
  (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

include hb₀ in
theorem quadLocalHom_eq_localPi (z : QE (algebraMap F Fv (d : F))) (w : PlaceSet (K := K) v) :
    quadLocalHom hb₁ v w.1 w.2 z = localPi bK v ![z.re, z.im] w := by
  rw [localPi_apply, Fin.sum_univ_two, hb₀,
    show ((1 : K) : w.1.adicCompletion K) = algebraMap K (w.1.adicCompletion K) 1 from rfl, map_one, one_mul]
  rfl

include hb₀ in
theorem quadLocalHom_injective {z z' : QE (algebraMap F Fv (d : F))}
    (h : ∀ w : PlaceSet (K := K) v, quadLocalHom hb₁ v w.1 w.2 z = quadLocalHom hb₁ v w.1 w.2 z') : z = z' := by
  have e : localPi bK v ![z.re, z.im] = localPi bK v ![z'.re, z'.im] := by
    funext w; rw [← quadLocalHom_eq_localPi hb₀ hb₁, ← quadLocalHom_eq_localPi hb₀ hb₁]; exact h w
  have e2 := localPi_injective bK v e
  have h0 := congrFun e2 0
  have h1 := congrFun e2 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  exact QuadraticAlgebra.ext h0 h1

include hb₀ in
theorem exists_quadLocalHom_eq (t : PlaceProd (K := K) v) :
    ∃ z : QE (algebraMap F Fv (d : F)), ∀ w : PlaceSet (K := K) v, quadLocalHom hb₁ v w.1 w.2 z = t w := by
  obtain ⟨c, hc⟩ := localPi_surjective bK v t
  refine ⟨⟨c 0, c 1⟩, fun w => ?_⟩
  rw [quadLocalHom_eq_localPi hb₀ hb₁, ← hc]
  have : (![(⟨c 0, c 1⟩ : QE (algebraMap F Fv (d : F))).re, (⟨c 0, c 1⟩ : QE (algebraMap F Fv (d : F))).im] :
      Fin 2 → Fv) = c := by funext i; fin_cases i <;> rfl
  rw [this]

include hb₀ in
theorem exists_quatLocalHom_eq (u : ∀ w : PlaceSet (K := K) v, QuatV (α : K) (β : K) w.1) :
    ∃ y : DEr Fv a b d, ∀ w : PlaceSet (K := K) v, quatLocalHom hb₁ hα hβ v w.1 w.2 y = u w := by
  obtain ⟨z0, h0⟩ := exists_quadLocalHom_eq hb₀ hb₁ v fun w => (u w).re
  obtain ⟨z1, h1⟩ := exists_quadLocalHom_eq hb₀ hb₁ v fun w => (u w).imI
  obtain ⟨z2, h2⟩ := exists_quadLocalHom_eq hb₀ hb₁ v fun w => (u w).imJ
  obtain ⟨z3, h3⟩ := exists_quadLocalHom_eq hb₀ hb₁ v fun w => (u w).imK
  exact ⟨⟨z0, z1, z2, z3⟩, fun w => QuaternionAlgebra.ext (h0 w) (h1 w) (h2 w) (h3 w)⟩

include hα in
theorem quadLocalHom_a' (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := F) w = v) :
    quadLocalHom hb₁ v w h (algebraMap Fv _ (algebraMap F Fv (a : F))) = algebraMap K (w.adicCompletion K) (α : K) :=
  quadLocalHom_a hb₁ hα v w h

theorem quadLocalHom_nrdE (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := F) w = v) (y : DEr Fv a b d) :
    quadLocalHom hb₁ v w h (nrdE y) = nrdLoc _ _ (quatLocalHom hb₁ hα hβ v w h y) := by
  rw [nrdLoc_eq_nrd]
  unfold nrdE
  simp only [map_add, map_sub, map_mul, map_pow]
  rw [quadLocalHom_a' hb₁ hα, quadLocalHom_a' hb₁ hβ]
  rfl

include hb₀ in
/-- **Elements of reduced norm $1$ at every $w\mid v$ come from $G^\natural(F_v)$.** -/
theorem exists_quatLocalUnit_eq (u : ∀ w : PlaceSet (K := K) v, (QuatV (α : K) (β : K) w.1)ˣ)
    (hu : ∀ w, nrdLoc _ _ (u w : QuatV (α : K) (β : K) w.1) = 1) :
    ∃ y : GnK Fv a b d, (nrdE ((y : DEK Fv a b d) : DEr Fv a b d) = 1) ∧
      ∀ w : PlaceSet (K := K) v, quatLocalUnit hb₁ hα hβ v w.1 w.2 y = u w := by
  obtain ⟨y0, hy0⟩ := exists_quatLocalHom_eq hb₀ hb₁ hα hβ v fun w => (u w : QuatV (α : K) (β : K) w.1)
  have hn : nrdE y0 = 1 := quadLocalHom_injective hb₀ hb₁ v fun w =>
    (quadLocalHom_nrdE hb₁ hα hβ v w.1 w.2 y0).trans (by rw [hy0 w, hu w]; exact (map_one _).symm)
  let Y : DEK Fv a b d := ⟨y0, star y0, by rw [mul_star_eq_nrdE, hn]; rfl, by rw [star_mul_eq_nrdE, hn]; rfl⟩
  have hY : Y ∈ Gnat (algebraMap F Fv (a : F)) (algebraMap F Fv (b : F)) (algebraMap F Fv (d : F)) := by
    change (nrdE y0).im = 0
    rw [hn]; rfl
  exact ⟨⟨Y, hY⟩, hn, fun w => Units.ext (hy0 w)⟩

end Lift

/-! ### Generic group facts -/

section GroupFacts

/-- The index of a product of subgroups is the product of the indices. Adapted from Mathlib's `Subgroup.index_pi`
(`Mathlib/GroupTheory/Index.lean`, Mathlib v4.35.0, Apache-2.0), which is stated for a constant family of groups; here the
family $G_i$ may depend on $i$ (same proof). -/
theorem index_pi_dep {ι : Type*} [Fintype ι] {G : ι → Type*} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i)) :
    (Subgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  simp_rw [Subgroup.index, ← Nat.card_pi]
  refine Nat.card_congr
    ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

/-- Conjugation by a scalar is trivial. -/
theorem conjOrth_scalar {F : Type} [Field F] [NumberField F] {K : Type*} [Field K] [Algebra F K] (Q : QuadForm F 3) {a b : F}
    (hQ : Q = pureForm a b) (r : Kˣ) :
    conjOrth (K := K) Q hQ (Units.map (algebraMap K (ℍ[K, algebraMap F K a, algebraMap F K b])).toMonoidHom r) = 1 := by
  set α := Units.map (algebraMap K (ℍ[K, algebraMap F K a, algebraMap F K b])).toMonoidHom r
  have hlin : conjLin α = LinearMap.id := by
    refine LinearMap.ext fun y => ?_
    rw [conjLin_apply, LinearMap.id_apply]
    have h1 : (α : ℍ[K, algebraMap F K a, algebraMap F K b]) * Quat.pure y = Quat.pure y * (α : ℍ[K, algebraMap F K a, algebraMap F K b]) :=
      Algebra.commutes _ _
    rw [h1, mul_assoc, Units.mul_inv, mul_one, imv_pure]
  apply Subtype.ext; apply Units.ext
  rw [conjOrth_coe, conjGL]
  change LinearMap.toMatrix' (conjLin α) = 1
  rw [hlin, LinearMap.toMatrix'_id]

theorem congSub_anti {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
    (Q₀ : QuadForm (𝓞 F) n) {m M : ℕ} (hm : 1 ≤ m) (hM : 1 ≤ M) (hmM : m ≤ M) :
    congSub v Q₀ M hM ≤ congSub v Q₀ m hm := fun _ hg i j =>
  (hg i j).trans (by rw [exp_le_exp]; omega)

theorem lamCong_anti {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (a b : 𝓞 F) {m M : ℕ}
    (hm : 1 ≤ m) (hM : 1 ≤ M) (hmM : m ≤ M) : lamCong v a b M hM ≤ lamCong v a b m hm := fun _ hu =>
  ⟨congSub_anti v _ hm hM hmM hu.1, hu.2⟩

end GroupFacts

/-! ### Test-set independence at a bad place -/

section Index

variable {F : Type} [Field F] [NumberField F] {a b d : 𝓞 F} {K : Type} [Field K] [NumberField K] [Algebra F K]
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  {α β : 𝓞 K} (hα : (α : K) = algebraMap F K (a : F)) (hβ : (β : K) = algebraMap F K (b : F))
  (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (ha0 : (a : F) ≠ 0) (hd0 : (d : F) ≠ 0) (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "Q₃" => QuatZeta.pureFormO α β
local notation "QF₃" => QuadForm.map (algebraMap (𝓞 K) K) (QuatZeta.pureFormO α β)

/-- **$Y^{(m)} = \{y\in G^\natural(F_v) : y_w\in\Lambda^{(m_w)}_w\ \forall w\mid v\}$ as a subgroup** (carrier `nsLoc`). -/
def nsLocSub (mK : HeightOneSpectrum (𝓞 K) → ℕ) (hmK1 : ∀ w, 1 ≤ mK w) : Subgroup (GnK Fv a b d) where
  carrier := nsLoc hb₁ hα hβ mK hmK1 v
  one_mem' w h := by simp
  mul_mem' hx hy w h := by rw [Subgroup.coe_mul, map_mul]; exact (lamCong w α β _ _).mul_mem (hx w h) (hy w h)
  inv_mem' hx w h := by rw [Subgroup.coe_inv, map_inv]; exact (lamCong w α β _ _).inv_mem (hx w h)

variable (α β) in
/-- $K^{(3)}_k\le SO(\langle-\alpha,-\beta,\alpha\beta\rangle)(K_w)$ as a subgroup (carrier `congSO3S`). -/
def k3Sub (w : HeightOneSpectrum (𝓞 K)) (k : ℕ) (hk : 1 ≤ k) : Subgroup (Measure.SOv w Q₃) :=
  (congSub w Q₃ k hk).comap (soSub QF₃ (w.adicCompletion K)).subtype

theorem isOpen_k3Sub (w : HeightOneSpectrum (𝓞 K)) (k : ℕ) (hk : 1 ≤ k) :
    IsOpen (k3Sub α β w k hk : Set (Measure.SOv w Q₃)) :=
  (isOpen_congSub w Q₃ k hk).preimage continuous_subtype_val

theorem isCompact_k3Sub (w : HeightOneSpectrum (𝓞 K)) (k : ℕ) (hk : 1 ≤ k) :
    IsCompact (k3Sub α β w k hk : Set (Measure.SOv w Q₃)) := by
  have hc : IsCompact (congSub w Q₃ k hk : Set (orthGroup QF₃ (w.adicCompletion K))) :=
    (isCompact_stdStab w QF₃).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ (isOpen_congSub w Q₃ k hk))
      (congSub_le_stdStab w Q₃ k hk)
  exact (isClosed_soSub w QF₃).isClosedEmbedding_subtypeVal.isCompact_preimage hc

variable (mK : HeightOneSpectrum (𝓞 K) → ℕ) (hmK1 : ∀ w, 1 ≤ mK w)

/-- **$y\mapsto(c(y_w))_{w\mid v}$**, $Y^{(m)}\to\prod_{w\mid v}K^{(3)}_{m_w}$. -/
def nsConjPi : nsLocSub hb₁ hα hβ v mK hmK1 →* ∀ w : PlaceSet (K := K) v, k3Sub α β w.1 (mK w.1) (hmK1 w.1) :=
  MonoidHom.pi fun w =>
    ((conjSOK (K := w.1.adicCompletion K) QF₃ (hQF α β)).comp ((quatLocalUnit hb₁ hα hβ v w.1 w.2).comp
      ((Gnat _ _ _).subtype.comp (nsLocSub hb₁ hα hβ v mK hmK1).subtype))).codRestrict _ fun y => (y.2 w.1 w.2).1

include hb₀ in
/-- **The map $Y^{(m)}\to\prod_{w\mid v}K^{(3)}_{m_w}$ is onto** at deep levels ($m_w\ge$ `nsLevK`). -/
theorem nsConjPi_surjective (hm : ∀ w, nsLevK hα0 hβ0 w ≤ mK w) :
    Function.Surjective (nsConjPi hb₁ hα hβ v mK hmK1) := by
  intro g
  have key : ∀ w : PlaceSet (K := K) v, ∃ u : (QuatV (α : K) (β : K) w.1)ˣ, u ∈ lamCong w.1 α β (mK w.1) (hmK1 w.1) ∧
      nrdLoc _ _ (u : QuatV (α : K) (β : K) w.1) = 1 ∧
      conjOrth QF₃ (hQF α β) u = ((g w : Measure.SOv w.1 Q₃) : orthGroup QF₃ (w.1.adicCompletion K)) := by
    intro w
    have hs := valued_two_eq w.1
    have hA := valued_eExp α hα0 w.1
    have hmw := hm w.1
    unfold nsLevK at hmw
    have h2s : 2 * sExp w.1 < mK w.1 := by omega
    have hmA : sExp w.1 + eExp α hα0 w.1 ≤ mK w.1 := by omega
    have hg : ((g w : Measure.SOv w.1 Q₃) : orthGroup QF₃ (w.1.adicCompletion K)) ∈
        (lamCong w.1 α β (mK w.1) (hmK1 w.1)).map (conjOrth QF₃ (hQF α β)) := by
      rw [map_lamCong w.1 α β hα0 hβ0 hs hA h2s hmA (hmK1 w.1)]; exact (g w).2
    obtain ⟨u, hu, hcu⟩ := hg
    obtain ⟨r, hr, hnr⟩ := isSq_nrdLoc_of_mem_lamCong w.1 α β hs hA h2s hmA (hmK1 w.1) hu
    have hr0 : r ≠ 0 := by intro h; rw [h, map_zero] at hr; exact zero_ne_one hr
    set c := Units.map (algebraMap (w.1.adicCompletion K) (QuatV (α : K) (β : K) w.1)).toMonoidHom (Units.mk0 r hr0)
    have hc : c ∈ lamCong w.1 α β (mK w.1) (hmK1 w.1) := scalar_mem_lamCong w.1 α β hs hA h2s hmA (hmK1 w.1) hr
    refine ⟨c⁻¹ * u, (lamCong w.1 α β _ _).mul_mem ((lamCong w.1 α β _ _).inv_mem hc) hu, ?_, ?_⟩
    · have hcn : nrdLoc _ _ (c : QuatV (α : K) (β : K) w.1) = r ^ 2 := nrdLoc_algebraMap w.1 α β r
      have hmul := nrdLoc_mul _ _ ((c⁻¹ : (QuatV (α : K) (β : K) w.1)ˣ) : QuatV (α : K) (β : K) w.1)
        (c : QuatV (α : K) (β : K) w.1)
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one, nrdLoc_one, hcn] at hmul
      rw [Units.val_mul, nrdLoc_mul, hnr]
      exact hmul.symm
    · rw [map_mul, map_inv, conjOrth_scalar, inv_one, one_mul, hcu]
  choose u hu using key
  obtain ⟨y, -, hy⟩ := exists_quatLocalUnit_eq hb₀ hb₁ hα hβ v u fun w => (hu w).2.1
  refine ⟨⟨y, fun w h => ?_⟩, ?_⟩
  · have := hy ⟨w, h⟩
    rw [this]; exact (hu ⟨w, h⟩).1
  · funext w
    apply Subtype.ext; apply Subtype.ext
    change conjOrth QF₃ (hQF α β) (quatLocalUnit hb₁ hα hβ v w.1 w.2 y) = _
    rw [hy w]; exact (hu w).2.2

/-- **$Y^{(M)}$ is the preimage of $\prod_{w\mid v}K^{(3)}_{M_w}$.** -/
theorem nsLocSub_subgroupOf (M : HeightOneSpectrum (𝓞 K) → ℕ) (hM1 : ∀ w, 1 ≤ M w) :
    (nsLocSub hb₁ hα hβ v M hM1).subgroupOf (nsLocSub hb₁ hα hβ v mK hmK1) =
      (Subgroup.pi Set.univ fun w : PlaceSet (K := K) v =>
        (k3Sub α β w.1 (M w.1) (hM1 w.1)).subgroupOf (k3Sub α β w.1 (mK w.1) (hmK1 w.1))).comap
        (nsConjPi hb₁ hα hβ v mK hmK1) := by
  ext y
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi, Set.mem_univ, true_implies]
  constructor
  · intro h w
    exact (h w.1 w.2).1
  · intro h w hw
    exact ⟨h ⟨w, hw⟩, (y.2 w hw).2⟩

include hb₀ in
/-- **$[Y^{(m)} : Y^{(M)}] = \prod_{w\mid v}[K^{(3)}_{m_w} : K^{(3)}_{M_w}]$** at deep levels. -/
theorem relIndex_nsLocSub (hm : ∀ w, nsLevK hα0 hβ0 w ≤ mK w) (M : HeightOneSpectrum (𝓞 K) → ℕ)
    (hM1 : ∀ w, 1 ≤ M w) :
    (nsLocSub hb₁ hα hβ v M hM1).relIndex (nsLocSub hb₁ hα hβ v mK hmK1) =
      ∏ w : PlaceSet (K := K) v, (k3Sub α β w.1 (M w.1) (hM1 w.1)).relIndex (k3Sub α β w.1 (mK w.1) (hmK1 w.1)) := by
  rw [Subgroup.relIndex, nsLocSub_subgroupOf,
    Subgroup.index_comap_of_surjective _ (nsConjPi_surjective hb₀ hb₁ hα hβ hα0 hβ0 v mK hmK1 hm), index_pi_dep]
  rfl

theorem nsLocSub_anti (M : HeightOneSpectrum (𝓞 K) → ℕ) (hM1 : ∀ w, 1 ≤ M w) (hmM : ∀ w, mK w ≤ M w) :
    nsLocSub hb₁ hα hβ v M hM1 ≤ nsLocSub hb₁ hα hβ v mK hmK1 := fun _ hy w h =>
  lamCong_anti w α β (hmK1 w) (hM1 w) (hmM w) (hy w h)

theorem quatLocalHom_scalar (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := F) w = v) (r : Fv) :
    quatLocalHom hb₁ hα hβ v w h ((algebraMap Fv (QE (algebraMap F Fv (d : F))) r : QE _) : DEr Fv a b d) =
      algebraMap (w.adicCompletion K) (QuatV (α : K) (β : K) w) (localRingHom v w h r) := by
  rw [QuaternionAlgebra.algebraMap_eq]
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
  · exact quadLocalHom_algebraMap hb₁ v w h r
  · exact map_zero _
  · exact map_zero _
  · exact map_zero _

/-- $U^{(m)}_v = \varphi(Y^{(m)})$ as a subgroup (carrier `nsU`). -/
def nsUSub : Subgroup (Measure.SOv v (qNS a b d)) :=
  (nsLocSub hb₁ hα hβ v mK hmK1).map (nsSOK Fv a b d ha0 hd0)

theorem coe_nsUSub : (nsUSub hb₁ hα hβ ha0 hd0 v mK hmK1 : Set (Measure.SOv v (qNS a b d))) =
    nsU hb₁ hα hβ ha0 hd0 mK hmK1 v := rfl

/-- **$[U^{(m)}_v : U^{(M)}_v] = [Y^{(m)} : Y^{(M)}]$**: the kernel of $\varphi$ on $Y^{(m)}$ consists of scalars, which lie in
$Y^{(M)}$. -/
theorem relIndex_nsUSub (hm : ∀ w, nsLevK hα0 hβ0 w ≤ mK w) (M : HeightOneSpectrum (𝓞 K) → ℕ)
    (hM1 : ∀ w, 1 ≤ M w) (hmM : ∀ w, mK w ≤ M w) :
    (nsUSub hb₁ hα hβ ha0 hd0 v M hM1).relIndex (nsUSub hb₁ hα hβ ha0 hd0 v mK hmK1) =
      (nsLocSub hb₁ hα hβ v M hM1).relIndex (nsLocSub hb₁ hα hβ v mK hmK1) := by
  set Y := nsLocSub hb₁ hα hβ v mK hmK1
  set Z := nsLocSub hb₁ hα hβ v M hM1
  have hZY : Z ≤ Y := nsLocSub_anti hb₁ hα hβ v mK hmK1 M hM1 hmM
  set f := (nsSOK Fv a b d ha0 hd0).comp Y.subtype
  have e1 : nsUSub hb₁ hα hβ ha0 hd0 v mK hmK1 = (⊤ : Subgroup Y).map f := by
    rw [← Subgroup.map_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype]; rfl
  have e2 : nsUSub hb₁ hα hβ ha0 hd0 v M hM1 = (Z.subgroupOf Y).map f := by
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hZY]; rfl
  have hker : f.ker ≤ Z.subgroupOf Y := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    obtain ⟨r, hr⟩ := (nsSOK_eq_one_iff ha0 hd0 (y : GnK Fv a b d)).1 hy
    rw [Subgroup.mem_subgroupOf]
    intro w h
    have hmw := hm w
    unfold nsLevK at hmw
    refine mem_lamCong_of_scalar w α β (valued_two_eq w) (valued_eExp α hα0 w) (by omega) (by omega) (hmK1 w)
      (hmM w) (y.2 w h) (r := localRingHom v w h r) ?_
    change quatLocalHom hb₁ hα hβ v w h (((y : GnK Fv a b d) : DEK Fv a b d) : DEr Fv a b d) = _
    rw [hr, quatLocalHom_scalar]
  rw [e1, e2, Subgroup.relIndex_map_map, sup_eq_left.2 hker, top_sup_eq, Subgroup.relIndex_top_right]
  rfl

end Index

/-! ### The named input at a deeper level, and the reduction -/

section Deep

theorem one_le_of_deep {K : Type} [Field K] [NumberField K] {α β : 𝓞 K} (hα0 : α ≠ 0) (hβ0 : β ≠ 0)
    {M : HeightOneSpectrum (𝓞 K) → ℕ} (hM : ∀ w, nsLevK hα0 hβ0 w ≤ M w) (w : HeightOneSpectrum (𝓞 K)) : 1 ≤ M w :=
  (one_le_nsLevK hα0 hβ0 w).trans (hM w)

variable (F : Type) [Field F] [NumberField F]

/-- **Input (named): the bad-place identity of the non-square model at some deeper level** (Weil 1982, Thm 2.3.1
[unverified page], in the test-set form of §2.2-2.3).

Fields:
- `ratio`: for every non-square model and every finite place $v$ of $F$ that is not `NSGoodPlace` (the data and the
  hypotheses of `NSBadPlaceRatio`), there are levels $M_w\ge m_w$ (= `nsLevK`) at the places $w$ of $K$ such that
  $$\Bigl(\prod_{w\mid v}\frac{\mu_w(K^{(3)}_{M_w})\,\omega_w(\mathcal O_w^\times)}{\omega_w(\operatorname{nrd}\Lambda^{(M_w)}_w)}\Bigr)\cdot
    \frac{\omega_v(N^{(M)}_v)}{\omega_v(\mathcal O_v^\times)} = r_v\cdot\mu^{SO}_v(U^{(M)}_v),$$
  the identity of `NSBadPlaceRatio` with the levels $m_w$ replaced by $M_w$ in $K^{(3)}$, $\Lambda^{(\cdot)}$, $N_v$ = `nsN` and
  $U_v$ = `nsU`.

The levels are free, so the comparison may be made on an arbitrarily small test set (Weil's gauge-form principle: the local
Haar ratio does not depend on the test set). `nsBadPlaceRatio_of_deep` proves that the identity at any deeper level gives
it at the level `nsLevK`. -/
@[kb "weil1982" "Thm 2.3.1 (local ratios) and §2.2-2.3 (test-set independence) [unverified page]"]
structure NSBadDeepRatio : Prop where
  ratio : ∀ (a b d : 𝓞 F) (K : Type) [Field K] [NumberField K] [Algebra F K]
    (bK : Module.Basis (Fin 2) F K) (_hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
    (α β : 𝓞 K) (hα : (α : K) = algebraMap F K (a : F)) (hβ : (β : K) = algebraMap F K (b : F))
    (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (_hna : IsTotallyPos (-(a : F))) (_hnb : IsTotallyPos (-(b : F)))
    (_hdpos : IsTotallyPos (d : F)) (v : HeightOneSpectrum (𝓞 F))
    (_hv : ¬ NSGoodPlace (bK := bK) (a := a) (b := b) (d := d) v),
    ∃ (M : HeightOneSpectrum (𝓞 K) → ℕ) (hM : ∀ w, nsLevK hα0 hβ0 w ≤ M w),
    (∏ w ∈ placesOver (K := K) v, Measure.muLocSO w (QuatZeta.pureFormO α β) 1
        (congSO3S (a := α) (b := β) M (one_le_of_deep hα0 hβ0 hM) w) *
      omegaV w (unitsVSub w) / omegaV w (nL α β M (one_le_of_deep hα0 hβ0 hM) w)) *
        (omegaV v (nsN α β M (one_le_of_deep hα0 hβ0 hM) v) / omegaV v (unitsVSub v)) =
      ENNReal.ofReal (nsRatio K a b d v) * Measure.muLocSO v (qNS a b d) 1
        (nsU hb₁ hα hβ (ne_zero_of_algebraMap_eq hα hα0) (d_ne_zero_of_basis hb₁) M (one_le_of_deep hα0 hβ0 hM) v)

variable {F}

set_option maxHeartbeats 1600000 in
/-- **Test-set independence of the bad-place ratio**: the identity at any deeper level gives the identity at the level
`nsLevK`, i.e. `NSBadDeepRatio F → NSBadPlaceRatio F`. Raising the level multiplies both sides by the same index
$\prod_{w\mid v}[K^{(3)}_{m_w} : K^{(3)}_{M_w}] = [U^{(m)}_v : U^{(M)}_v]$ (`relIndex_nsLocSub`, `relIndex_nsUSub`), and leaves
$\operatorname{nrd}\Lambda^{(\cdot)}_w = \mathcal O_w^{\times2}$ and $N_v$ unchanged (`nL_eq_sqUnits`). -/
@[kb "weil1982" "Thm 2.3.1 and §2.2-2.3 (the local ratio is independent of the test set) [unverified page]"]
theorem nsBadPlaceRatio_of_deep (hD : NSBadDeepRatio F) : NSBadPlaceRatio F := by
  refine ⟨fun a b d K _ _ _ bK hb₀ hb₁ α β hα hβ hα0 hβ0 hna hnb hdpos v hv => ?_⟩
  obtain ⟨M, hM, hEq⟩ := hD.ratio a b d K bK hb₀ hb₁ α β hα hβ hα0 hβ0 hna hnb hdpos v hv
  have ha0 := ne_zero_of_algebraMap_eq hα hα0
  have hb0 := ne_zero_of_algebraMap_eq hβ hβ0
  have hd0 := d_ne_zero_of_basis hb₁
  have hm1 : ∀ w, 1 ≤ nsLevK hα0 hβ0 w := one_le_nsLevK hα0 hβ0
  have hM1 : ∀ w, 1 ≤ M w := one_le_of_deep hα0 hβ0 hM
  have hmm : ∀ w, nsLevK hα0 hβ0 w ≤ nsLevK hα0 hβ0 w := fun w => le_rfl
  -- the reduced norms and `N_v` do not change
  have hnL : ∀ w, nL α β M hM1 w = nL α β (nsLevK hα0 hβ0) hm1 w := fun w => by
    have h1 : 2 * (3 * sExp w + 2 * eExp α hα0 w + 2 * eExp β hβ0 w) + 1 ≤ M w := hM w
    have h2 : nsLevK hα0 hβ0 w = 2 * (3 * sExp w + 2 * eExp α hα0 w + 2 * eExp β hβ0 w) + 1 := rfl
    rw [nL_eq_sqUnits M hM1 hα0 w (by omega) (by omega),
      nL_eq_sqUnits (nsLevK hα0 hβ0) hm1 hα0 w (by omega) (by omega)]
  have hN : nsN α β M hM1 v = nsN α β (nsLevK hα0 hβ0) hm1 v := by
    ext r
    simp only [nsN, Set.mem_ofPred_eq, hnL]
  -- the congruence subgroups of `SO₃`
  set I : HeightOneSpectrum (𝓞 K) → ℝ≥0∞ := fun w =>
    ((k3Sub α β w (M w) (hM1 w)).relIndex (k3Sub α β w (nsLevK hα0 hβ0 w) (hm1 w)) : ℝ≥0∞) with hIdef
  have hK3 : ∀ w, Measure.muLocSO w (QuatZeta.pureFormO α β) 1 (congSO3S (a := α) (b := β) (nsLevK hα0 hβ0) hm1 w) =
      I w * Measure.muLocSO w (QuatZeta.pureFormO α β) 1 (congSO3S (a := α) (b := β) M hM1 w) := fun w => by
    have : IsMulLeftInvariant (Measure.muLocSO w (QuatZeta.pureFormO α β) 1) := by
      unfold Measure.muLocSO; infer_instance
    exact measure_subgroup_eq_relIndex_mul _ (isOpen_k3Sub (α := α) (β := β) w (M w) (hM1 w))
      (fun g hg => congSub_anti w _ (hm1 w) (hM1 w) (hM w) hg)
      (relIndex_ne_zero_of_isOpen (isCompact_k3Sub (α := α) (β := β) w (nsLevK hα0 hβ0 w) (hm1 w)) (isOpen_k3Sub (α := α) (β := β) w (M w) (hM1 w)))
  -- the image `U_v`
  have hint := isIntegral_basis hb₀ hb₁
  have hvS : v ∈ nsBad (bK := bK) ha0 hb0 hd0 := (Set.Finite.mem_toFinset _).2 hv
  have hUo : IsOpen (nsU hb₁ hα hβ ha0 hd0 M hM1 v) :=
    isOpen_nsU hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 (nsBad (bK := bK) ha0 hb0 hd0)
      (nsBadK (K := K) (nsBad (bK := bK) ha0 hb0 hd0)) M hM1 hb0 hint (fun w => mem_nsBadK)
      (fun v hv => nsGood_of_not_mem bK hv) hvS
  have hidx := relIndex_nsLocSub hb₀ hb₁ hα hβ hα0 hβ0 v (nsLevK hα0 hβ0) hm1 hmm M hM1
  have hidxU := relIndex_nsUSub hb₁ hα hβ hα0 hβ0 ha0 hd0 v (nsLevK hα0 hβ0) hm1 hmm M hM1 hM
  have hU : Measure.muLocSO v (qNS a b d) 1 (nsU hb₁ hα hβ ha0 hd0 (nsLevK hα0 hβ0) hm1 v) =
      (∏ w ∈ placesOver (K := K) v, I w) * Measure.muLocSO v (qNS a b d) 1 (nsU hb₁ hα hβ ha0 hd0 M hM1 v) := by
    have : IsMulLeftInvariant (Measure.muLocSO v (qNS a b d) 1) := by unfold Measure.muLocSO; infer_instance
    have hfin : (nsUSub hb₁ hα hβ ha0 hd0 v M hM1).relIndex (nsUSub hb₁ hα hβ ha0 hd0 v (nsLevK hα0 hβ0) hm1) ≠ 0 := by
      rw [hidxU, hidx, Finset.prod_ne_zero_iff]
      exact fun w _ => relIndex_ne_zero_of_isOpen (isCompact_k3Sub (α := α) (β := β) w.1 (nsLevK hα0 hβ0 w.1) (hm1 w.1))
        (isOpen_k3Sub (α := α) (β := β) w.1 (M w.1) (hM1 w.1))
    have e := measure_subgroup_eq_relIndex_mul (Measure.muLocSO v (qNS a b d) 1) (A := nsUSub hb₁ hα hβ ha0 hd0 v (nsLevK hα0 hβ0) hm1)
      (B := nsUSub hb₁ hα hβ ha0 hd0 v M hM1) hUo
      (Subgroup.map_mono (nsLocSub_anti hb₁ hα hβ v (nsLevK hα0 hβ0) hm1 M hM1 hM)) hfin
    rw [coe_nsUSub, coe_nsUSub, hidxU, hidx, Nat.cast_prod] at e
    rw [e, Finset.prod_subtype (placesOver (K := K) v) (fun w => mem_placesOver v) I]
  -- assembly
  rw [hU, ← hN]
  simp_rw [← hnL, hK3]
  have hsplit : ∀ w ∈ placesOver (K := K) v, I w * Measure.muLocSO w (QuatZeta.pureFormO α β) 1
      (congSO3S (a := α) (b := β) M hM1 w) * omegaV w (unitsVSub w) / omegaV w (nL α β M hM1 w) =
      I w * (Measure.muLocSO w (QuatZeta.pureFormO α β) 1 (congSO3S (a := α) (b := β) M hM1 w) *
        omegaV w (unitsVSub w) / omegaV w (nL α β M hM1 w)) := fun w _ => by
    simp only [div_eq_mul_inv, mul_assoc]
  rw [Finset.prod_congr rfl hsplit, Finset.prod_mul_distrib, mul_assoc, hEq]
  ring

open QuadFormsKB.HilbertModular in
/-- **`GnatMeasureComparisonNSDef F`** from the bad-place identity at some deeper level. -/
@[kb "weil1982" "Thm 2.3.1 [unverified page]"]
theorem gnatMeasureComparisonNS_of_deep [IsTotallyReal F] (hD : NSBadDeepRatio F) : GnatMeasureComparisonNSDef F :=
  gnatMeasureComparisonNS_of_ratio (nsBadPlaceRatio_of_deep hD)

open QuadFormsKB.HilbertModular in
/-- **$\tau(SO_4) = 2$ for every totally real $F$**, from `NSBadDeepRatio F`. -/
@[kb "weil1982" "§3.7, Thm 3.7.1 (m = 4), p. 65; Thm 2.3.1"]
theorem quaternaryTamagawaTwo_of_deep [IsTotallyReal F] (hD : NSBadDeepRatio F) : QuaternaryTamagawaTwo F :=
  quaternaryTamagawaTwo_of_ratio (nsBadPlaceRatio_of_deep hD)

open QuadFormsKB.HilbertModular in
/-- **`RankFourUnitSiegel F`** from `NSBadDeepRatio F`. -/
@[kb "weil1982" "§4.5, p. 100; §3.7; Thm 2.3.1"]
theorem rankFourUnitSiegel_of_deep [IsTotallyReal F] (hD : NSBadDeepRatio F) : RankFourUnitSiegel F :=
  rankFourUnitSiegel_of_ratio (nsBadPlaceRatio_of_deep hD)

open QuadFormsKB.HilbertModular in
/-- **Siegel's formula for every totally positive definite form over $\mathcal O_F$ in every rank $N\ge4$, every totally
positive $m$, every totally real $F$** (any class number), from `NSBadDeepRatio F`. -/
@[kb "siegel1935" "Hauptsatz [unverified]; weil1982 §4.5, Thm 4.5.1"]
theorem siegelFormulaAt_totallyReal_of_deep [IsTotallyReal F] (hD : NSBadDeepRatio F) {N : ℕ} (hN : 4 ≤ N)
    (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F}
    (hm : ∀ v, 0 < QuadFormsKB.HilbertModular.realEmb F v (algebraMap (𝓞 F) F m)) : SiegelFormulaAt Q₀ m :=
  siegelFormulaAt_totallyReal_of_ratio (nsBadPlaceRatio_of_deep hD) hN Q₀ hpd hm

open QuadFormsKB.HilbertModular in
/-- **$\tau = 2$ in every rank $N\ge4$**, from `NSBadDeepRatio F`. -/
@[kb "weil1982" "Thm 3.7.1, Thm 4.5.1, p. 109; Thm 2.3.1"]
theorem tamagawaNumberTwo_all_ranks_of_deep [IsTotallyReal F] (hD : NSBadDeepRatio F) {N : ℕ} (hN : 4 ≤ N)
    (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀)) : TamagawaNumberTwo Q₀ :=
  tamagawaNumberTwo_all_ranks_of_ratio (nsBadPlaceRatio_of_deep hD) hN Q₀ hpd

open QuadFormsKB.HilbertModular in
/-- **The mass formula in every rank $N\ge4$**, from `NSBadDeepRatio F`. -/
@[kb "weil1982" "Thm 4.5.1, p. 109; Thm 2.3.1"]
theorem massFormula_all_ranks_of_deep [IsTotallyReal F] (hD : NSBadDeepRatio F) {N : ℕ} (hN : 4 ≤ N)
    (Q₀ : QuadForm (𝓞 F) N) (hpd : IsTotallyPosDef (formF Q₀)) : MassFormulaHolds Q₀ :=
  massFormula_all_ranks_of_ratio (nsBadPlaceRatio_of_deep hD) hN Q₀ hpd

end Deep

/-! ### The gauge-form volume of $K_N$ for $\langle1,-ad,-bd,abd\rangle$ -/

section VolQNS

open LocalDensity LocalZeta

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {a b d : 𝓞 F}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem hessian_Qp_qNS' (a b d : 𝓞 F) : (NF.Qp v (qNS a b d)).hessian =
    Matrix.diagonal (fun i => NF.ι v (![2, -2 * (a * d), -2 * (b * d), 2 * (a * (b * d))] i)) := by
  rw [NF.Qp, QuadForm.hessian_map, hessian_qNS, Matrix.diagonal_map (map_zero _), mul_assoc a b d]

theorem valued_algebraMap_mul {x y : 𝓞 F} {ex ey : ℕ} (hx : Valued.v (algebraMap F Fv (x : F)) = exp (-(ex : ℤ)))
    (hy : Valued.v (algebraMap F Fv (y : F)) = exp (-(ey : ℤ))) :
    Valued.v (algebraMap F Fv ((x * y : 𝓞 F) : F)) = exp (-((ex + ey : ℕ) : ℤ)) := by
  rw [show ((x * y : 𝓞 F) : F) = (x : F) * (y : F) by push_cast; ring, map_mul, map_mul, hx, hy, ← exp_add]
  congr 1; push_cast; ring

/-- **The gauge-form volume of $K_N$ for $\langle1,-ad,-bd,abd\rangle$** ($N\ge 2(4s+2e_a+2e_b+3e_d)+1$):
$\mu_v(K_N)\cdot q^{6N} = q^{10s+3e_a+3e_b+6e_d+\min(e_a,e_b)}$ (the linear count `muLoc_congSub_eq`, as for
`muLoc_congSub_qSq_mul`). -/
@[kb "weil1982" "§2.2 (gauge-form volumes by counting) [unverified]"]
theorem muLoc_congSub_qNS_mul {s eA eB eD m : ℕ} (hQ : (qNS a b d).Nondegenerate)
    (hs : Valued.v (2 : Fv) = exp (-(s : ℤ))) (hA : Valued.v (algebraMap F Fv (a : F)) = exp (-(eA : ℤ)))
    (hB : Valued.v (algebraMap F Fv (b : F)) = exp (-(eB : ℤ)))
    (hD : Valued.v (algebraMap F Fv (d : F)) = exp (-(eD : ℤ))) (hm : 2 * (4 * s + 2 * eA + 2 * eB + 3 * eD) + 1 ≤ m) :
    Measure.muLoc v (qNS a b d) 1 (congSub v (qNS a b d) m (by omega) : Set _) * (DVR.q 𝔬 : ℝ≥0∞) ^ (6 * m) =
      (DVR.q 𝔬 : ℝ≥0∞) ^ (10 * s + 3 * eA + 3 * eB + 6 * eD + min eA eB) := by
  set dd := 4 * s + 2 * eA + 2 * eB + 3 * eD
  set j := 2 * dd + 1
  set μ := min eA eB
  have hq0 : (DVR.q 𝔬 : ℝ≥0∞) ≠ 0 := by exact_mod_cast (q_pos v).ne'
  have hqt : (DVR.q 𝔬 : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  set h : Fin 4 → 𝔬 := fun i => NF.ι v (![2, -2 * (a * d), -2 * (b * d), 2 * (a * (b * d))] i)
  set e : Fin 4 → ℕ := ![s, s + (eA + eD), s + (eB + eD), s + eA + (eB + eD)]
  have hval : ∀ i, Valued.v ((h i : 𝔬) : Fv) = exp (-(e i : ℤ)) := by
    intro i
    fin_cases i
    · exact valued_ι_two hs
    · exact valued_ι_neg_two_mul hs (valued_algebraMap_mul hA hD)
    · exact valued_ι_neg_two_mul hs (valued_algebraMap_mul hB hD)
    · exact valued_ι_two_mul_mul hs hA (valued_algebraMap_mul hB hD)
  have hdiv := fun i => pow_dvd_of_valued (hval i)
  have hdet : Valued.v (((NF.Qp v (qNS a b d)).hessian.det : 𝔬) : Fv) = exp (-(dd : ℤ)) := by
    rw [hessian_Qp_qNS', Matrix.det_diagonal, Fin.prod_univ_four]
    change Valued.v ((h 0 : Fv) * (h 1 : Fv) * (h 2 : Fv) * (h 3 : Fv)) = _
    rw [map_mul, map_mul, map_mul, hval 0, hval 1, hval 2, hval 3, ← WithZero.exp_add, ← WithZero.exp_add,
      ← WithZero.exp_add]
    congr 1; simp [dd, e]; ring
  obtain ⟨hd, hd'⟩ := pow_dvd_of_valued hdet
  rw [muLoc_congSub_eq v _ hQ m (by omega) dd j hd hd' le_rfl (by omega),
    card_kerD_diag4 v _ h (hessian_Qp_qNS' a b d) j e (fun i => (hdiv i).1) (fun i => (hdiv i).2)
      (fun i => by
        have : e i ≤ s + eA + (eB + eD) := by fin_cases i <;> simp [e] <;> omega
        omega)]
  have he0 : e 0 = s := rfl
  have he1 : e 1 = s + (eA + eD) := rfl
  have he2 : e 2 = s + (eB + eD) := rfl
  have he3 : e 3 = s + eA + (eB + eD) := rfl
  have m01 : min (e 0) (e 1) = s := by rw [he0, he1]; exact min_eq_left (by omega)
  have m02 : min (e 0) (e 2) = s := by rw [he0, he2]; exact min_eq_left (by omega)
  have m03 : min (e 0) (e 3) = s := by rw [he0, he3]; exact min_eq_left (by omega)
  have m12 : min (e 1) (e 2) = s + (μ + eD) := by rw [he1, he2, min_add_add_left, min_add_add_right]
  have m13 : min (e 1) (e 3) = s + (eA + eD) := by rw [he1, he3]; exact min_eq_left (by omega)
  have m23 : min (e 2) (e 3) = s + (eB + eD) := by rw [he2, he3]; exact min_eq_left (by omega)
  rw [m01, m02, m03, m12, m13, m23, he0, he1, he2, he3]
  set q := (DVR.q 𝔬 : ℝ≥0∞)
  simp only [Nat.cast_pow, ← pow_add]
  rw [show (4 * (4 - 1) / 2) = 6 by norm_num,
    show s + (s + (eA + eD)) + (s + (eB + eD)) + (s + eA + (eB + eD)) + (s + j + (s + j) + (s + j) +
      (s + (μ + eD) + j) + (s + (eA + eD) + j) + (s + (eB + eD) + j)) =
      (10 * s + 3 * eA + 3 * eB + 6 * eD + μ) + 6 * j by ring,
    show (m + j) * 6 = 6 * j + 6 * m by ring, pow_add, pow_add q (6 * j), div_eq_mul_inv,
    ENNReal.mul_inv (Or.inl (pow_ne_zero _ hq0)) (Or.inl (ENNReal.pow_ne_top hqt))]
  calc q ^ (10 * s + 3 * eA + 3 * eB + 6 * eD + μ) * q ^ (6 * j) * ((q ^ (6 * j))⁻¹ * (q ^ (6 * m))⁻¹) * q ^ (6 * m)
      = q ^ (10 * s + 3 * eA + 3 * eB + 6 * eD + μ) * (q ^ (6 * j) * (q ^ (6 * j))⁻¹) *
          ((q ^ (6 * m))⁻¹ * q ^ (6 * m)) := by ring
    _ = _ := by
      rw [ENNReal.mul_inv_cancel (pow_ne_zero _ hq0) (ENNReal.pow_ne_top hqt),
        ENNReal.inv_mul_cancel (pow_ne_zero _ hq0) (ENNReal.pow_ne_top hqt), mul_one, mul_one]

end VolQNS

end

end QuadFormsKB.Tamagawa.Measure.Weil
